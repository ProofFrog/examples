(* ==================================================================== *)
(* RandomTargetGuessing: comparing against a hidden uniform target        *)
(*                                                                        *)
(* EasyCrypt proof of the ProofFrog statistical helper game pair in the    *)
(* co-located RandomTargetGuessing.game:                                   *)
(*                                                                        *)
(*   Real.Initialize()  : target <- S    (uniform, never revealed)        *)
(*   Real.Eq(c)         : return c == target                              *)
(*   Ideal.Eq(c)        : return false                                    *)
(*                                                                        *)
(* The game is honest as stated: any adversary making at most q Eq        *)
(* queries distinguishes Real from Ideal with advantage at most q/|S|.    *)
(*                                                                        *)
(* Proof shape.  A bridge game GuessO samples a target like Real but      *)
(* answers false like Ideal:                                              *)
(*   - Real vs Guess is identical-until-bad, where bad is "some query     *)
(*     hit the target" (mem log target for the wrapper's query log);      *)
(*   - Guess vs Ideal is a perfect equivalence (the target is dead code); *)
(*   - Pr[Guess : bad] <= q/|S| is the guessing bound.  fel does NOT      *)
(*     apply here (the oracle does no sampling; once the target is fixed  *)
(*     the per-query event is deterministic), so we instead swap the      *)
(*     unused target sample past the adversary run (eager -> lazy) and    *)
(*     bound the probability that a fresh uniform draw lands in the       *)
(*     query log of size <= q.                                            *)
(*                                                                        *)
(* Like SamplingWithoutReplacement.ec, the wrapper enforces the query     *)
(* budget q and the bound is one-sided over an arbitrary predicate P on    *)
(* the output (which is how exported assumption hops consume it).          *)
(* ==================================================================== *)

require import AllCore List FSet Distr StdOrder.
(*---*) import RealOrder.
require import Mu_mem.

(* The finite sample space S, with its uniform distribution dS. *)
type S.

clone import MFinite as FinS with type t <- S.

op dS : S distr = FinS.dunifin.
op cardS : int = FinS.Support.card.

lemma dS_ll : is_lossless dS.
proof. exact FinS.dunifin_ll. qed.

lemma dS1E (x : S) : mu1 dS x = 1%r / cardS%r.
proof. exact FinS.dunifin1E. qed.

lemma cardS_gt0 : 0 < cardS.
proof. exact FinS.Support.card_gt0. qed.

(* Key measure: the probability a uniform sample lands in a set. *)
lemma mu_dS_mem (X : S fset) : mu dS (mem X) <= (card X)%r / cardS%r.
proof.
have -> : (card X)%r / cardS%r = (card X)%r * (1%r / cardS%r) by smt().
apply (mu_mem_le X dS (1%r / cardS%r)).
move=> x _; rewrite dS1E //.
qed.

(* maximum number of Eq queries the adversary may make *)
op q : { int | 0 <= q } as q_ge0.

(* -------------------------------------------------------------------- *)
(* Module interfaces.                                                     *)
(* -------------------------------------------------------------------- *)

module type EqOracle = {
  proc eq(c : S) : bool
}.

module type Adv (O : EqOracle) = {
  proc run() : bool { O.eq }
}.

(* The raw oracle the experiment wraps. *)
module type RawEq = {
  proc init() : unit
  proc f(c : S) : bool
}.

(* Real world: compare against a hidden uniform target. *)
module RealO : RawEq = {
  var target : S
  proc init() : unit = { target <$ dS; }
  proc f(c : S) : bool = { return c = target; }
}.

(* Ideal world: always false (matches the .game's Ideal exactly). *)
module IdealO : RawEq = {
  proc init() : unit = { }
  proc f(c : S) : bool = { return false; }
}.

(* Bridge: samples a target like RealO, answers like IdealO.  Its f never
   reads the target, which is what lets the target sample move past the
   adversary run in the lazy-sampling step. *)
module GuessO : RawEq = {
  var target : S
  proc init() : unit = { target <$ dS; }
  proc f(c : S) : bool = { return false; }
}.

(* The bounded-query experiment: counts queries and logs them. *)
module Exp (O : RawEq) (A : Adv) = {
  module WO : EqOracle = {
    var cO  : int
    var log : S fset

    proc init() : unit = {
      cO  <- 0;
      log <- fset0;
      O.init();
    }

    proc eq(c : S) : bool = {
      var r;
      r <- false;
      if (cO < q) {
        r   <@ O.f(c);
        log <- log `|` fset1 c;
        cO  <- cO + 1;
      }
      return r;
    }
  }

  proc main() : bool = {
    var r;
    WO.init();
    r <@ A(WO).run();
    return r;
  }
}.

(* Lazy variant of Exp(GuessO): same adversary run (GuessO.f never reads
   the target), target sampled after the run; returns the bad event. *)
module ExpLazy (A : Adv) = {
  proc main() : bool = {
    var r, t;
    Exp.WO.cO  <- 0;
    Exp.WO.log <- fset0;
    r <@ A(Exp(GuessO, A).WO).run();
    t <$ dS;
    return mem Exp.WO.log t;
  }
}.

(* -------------------------------------------------------------------- *)
(* Step 1: Real is identical to Guess until a query hits the target.      *)
(* -------------------------------------------------------------------- *)

lemma pr_Real_Guess &m (A <: Adv {-Exp, -RealO, -IdealO, -GuessO})
    (P : bool -> bool) :
  (forall (O <: EqOracle{-A}), islossless O.eq => islossless A(O).run) =>
  Pr[Exp(RealO, A).main() @ &m : P res]
  <= Pr[Exp(GuessO, A).main() @ &m :
          P res \/ mem Exp.WO.log GuessO.target].
proof.
move=> A_ll.
byequiv (: ={glob A} ==>
           !(mem Exp.WO.log GuessO.target){2} => ={res}) => //; last by smt().
proc.
call (: mem Exp.WO.log GuessO.target,
        ={Exp.WO.cO, Exp.WO.log} /\ RealO.target{1} = GuessO.target{2},
        true).
+ proc; sp; if => //.
  inline *; auto => />; smt(in_fsetU in_fset1).
+ move=> &2 bad_h; proc; sp; if => //.
  by inline *; auto.
+ move=> _; proc; sp; if => //.
  by inline *; auto => />; smt(in_fsetU).
inline *; auto => /> /#.
qed.

(* -------------------------------------------------------------------- *)
(* Step 2: Guess and Ideal are perfectly equivalent (dead target).        *)
(* -------------------------------------------------------------------- *)

lemma pr_Guess_Ideal &m (A <: Adv {-Exp, -RealO, -IdealO, -GuessO})
    (P : bool -> bool) :
  Pr[Exp(GuessO, A).main() @ &m : P res]
  = Pr[Exp(IdealO, A).main() @ &m : P res].
proof.
byequiv (: ={glob A} ==> ={res}) => //.
proc.
call (: ={Exp.WO.cO, Exp.WO.log}).
+ proc; sp; if => //.
  by inline *; auto.
by inline *; auto.
qed.

(* -------------------------------------------------------------------- *)
(* Step 3: the guessing bound.  Eager -> lazy, then a one-shot mu bound.  *)
(* -------------------------------------------------------------------- *)

lemma pr_Guess_Lazy &m (A <: Adv {-Exp, -RealO, -IdealO, -GuessO}) :
  Pr[Exp(GuessO, A).main() @ &m : mem Exp.WO.log GuessO.target]
  = Pr[ExpLazy(A).main() @ &m : res].
proof.
byequiv (: ={glob A} ==>
           (mem Exp.WO.log GuessO.target){1} = res{2}) => //.
proc.
inline *; wp.
swap{1} 3 1.
rnd; call (: ={Exp.WO.cO, Exp.WO.log}).
+ proc; sp; if => //.
  by inline *; auto.
by auto.
qed.

lemma pr_Lazy_bound &m (A <: Adv {-Exp, -RealO, -IdealO, -GuessO}) :
  Pr[ExpLazy(A).main() @ &m : res] <= q%r / cardS%r.
proof.
byphoare => //.
proc.
seq 3 : (card Exp.WO.log <= q) 1%r (q%r / cardS%r) 0%r _ => //.
+ (* the suffix: a fresh uniform draw lands in a set of size <= q *)
  wp; rnd; skip => /> &hr hcard.
  have h := mu_dS_mem Exp.WO.log{hr}.
  apply (ler_trans ((card Exp.WO.log{hr})%r / cardS%r)) => //.
  smt(cardS_gt0).
+ (* the prefix always keeps the log within the query budget *)
  hoare.
  call (: card Exp.WO.log <= Exp.WO.cO /\ Exp.WO.cO <= q).
  + proc; sp; if => //.
    inline *; auto => />; smt(fcardU fcard1 fcard_ge0).
  by auto => />; smt(fcards0 q_ge0).
qed.

(* -------------------------------------------------------------------- *)
(* The advantage bound: adv <= q / |S|.                                   *)
(* -------------------------------------------------------------------- *)

lemma adv_bound &m (A <: Adv {-Exp, -RealO, -IdealO, -GuessO})
    (P : bool -> bool) :
  (forall (O <: EqOracle{-A}), islossless O.eq => islossless A(O).run) =>
  Pr[Exp(RealO, A).main() @ &m : P res]
  <= Pr[Exp(IdealO, A).main() @ &m : P res] + q%r / cardS%r.
proof.
move=> A_ll.
apply (ler_trans (Pr[Exp(GuessO, A).main() @ &m :
                       P res \/ mem Exp.WO.log GuessO.target])).
+ exact (pr_Real_Guess &m A P A_ll).
apply (ler_trans (Pr[Exp(GuessO, A).main() @ &m : P res]
                + Pr[Exp(GuessO, A).main() @ &m :
                       mem Exp.WO.log GuessO.target])).
+ by rewrite Pr [mu_or]; smt(ge0_mu).
rewrite (pr_Guess_Ideal &m A P).
have mono : forall (a b c : real), b <= c => a + b <= a + c by smt().
apply mono.
by rewrite (pr_Guess_Lazy &m A); exact (pr_Lazy_bound &m A).
qed.
