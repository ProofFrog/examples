(* ==================================================================== *)
(* PRPPRFSwitching: random permutation vs random function                 *)
(*                                                                        *)
(* EasyCrypt proof of the ProofFrog statistical helper game pair in the    *)
(* co-located PRPPRFSwitching.game (the information-theoretic PRP/PRF       *)
(* switching lemma):                                                       *)
(*                                                                        *)
(*   RandomFunction.Eval(x) : memoised; fresh outputs y <- Y      (w/ repl)*)
(*   Permutation.Eval(x)    : memoised; fresh outputs y <-uniq Y  (w/o)    *)
(*                                                                        *)
(* Over q distinct queries the two are indistinguishable up to the        *)
(* birthday bound:                                                         *)
(*                                                                        *)
(*   adv <= q (q - 1) / (2 |Y|).                                          *)
(*                                                                        *)
(* This is the DistinctSampling birthday fact (SamplingWithoutReplacement *)
(* .ec, adv_bound_birthday) lifted through an input-memoising map: cache  *)
(* hits are identical on both sides and do not sample, so the experiment  *)
(* reduces to the sequence of FRESH-output draws, which is exactly        *)
(* with-replacement (RandomFunction) vs without-replacement (Permutation) *)
(* sampling.  The excluded set is the game's OWN output image `used`, of   *)
(* cardinality = the fresh-query count, so the per-query cap is the        *)
(* identity (linear) cap -- the birthday shape -- with no caller input.   *)
(*                                                                        *)
(* Modeling notes.                                                        *)
(*  - Output type Y is finite and uniform (Y = BitString<n> in the game,  *)
(*    |Y| = 2^n).  The input type X is arbitrary.                          *)
(*  - The experiment wrapper enforces a query budget q, as in             *)
(*    SamplingWithoutReplacement.ec.  We need q <= |Y| so the             *)
(*    without-replacement resample is lossless (you cannot draw more      *)
(*    distinct points than the domain holds).                             *)
(*  - The bound is one-sided over an arbitrary output predicate P (the    *)
(*    shape exported assumption hops consume): we prove RandomFunction    *)
(*    (with replacement) on the left, Permutation on the right.           *)
(* ==================================================================== *)

require import AllCore List FSet FMap Distr StdOrder StdBigop.
(*---*) import RealOrder Bigreal BRA.
require import Dexcepted Mu_mem.
require import FelTactic.

(* Input (query) type: arbitrary. *)
type X.

(* Output type: a finite type with its uniform distribution dY. *)
type Y.

clone import MFinite as FinY with type t <- Y.

op dY : Y distr = FinY.dunifin.
op cardY : int = FinY.Support.card.

lemma dY_ll : is_lossless dY.
proof. exact FinY.dunifin_ll. qed.

lemma dY1E (y : Y) : mu1 dY y = 1%r / cardY%r.
proof. exact FinY.dunifin1E. qed.

lemma cardY_gt0 : 0 < cardY.
proof. exact FinY.Support.card_gt0. qed.

(* Key per-query measure: the probability a uniform sample lands in a set.*)
lemma mu_dY_mem (S : Y fset) : mu dY (mem S) <= (card S)%r / cardY%r.
proof.
have -> : (card S)%r / cardY%r = (card S)%r * (1%r / cardY%r) by smt().
apply (mu_mem_le S dY (1%r / cardY%r)).
move=> y _; rewrite dY1E //.
qed.

(* -------------------------------------------------------------------- *)
(* Experiment parameters.                                                 *)
(* -------------------------------------------------------------------- *)

(* maximum number of (distinct) queries the adversary may make *)
op q : { int | 0 <= q } as q_ge0.

(* The budget must not exceed the domain, else a random permutation runs  *)
(* out of fresh outputs (and the ideal resample stops being lossless).    *)
axiom q_le_card : q <= cardY.

(* per-query bad-event rate: at the k-th fresh query the output image has  *)
(* k elements, so a with-replacement draw collides with probability k/|Y|. *)
op g (k : int) : real = k%r / cardY%r.

(* -------------------------------------------------------------------- *)
(* Module interfaces.                                                     *)
(* -------------------------------------------------------------------- *)

module type Oracle = {
  proc eval(x : X) : Y
}.

module type Adv (O : Oracle) = {
  proc run() : bool { O.eval }
}.

(* The "raw" fresh-output sampler the experiment wraps: returns the        *)
(* sampled output together with the bad bit (did the with-replacement      *)
(* draw land in the current output image).                                 *)
module type RawOracle = {
  proc init() : unit
  proc f() : Y * bool
}.

(* Shared game state: the input->output memo table and its output image. *)
module Mem = {
  var t    : (X, Y) fmap
  var used : Y fset
}.

(* RandomFunction: fresh outputs sampled WITH replacement. *)
module RealO : RawOracle = {
  proc init() : unit = { Mem.t <- empty; Mem.used <- fset0; }
  proc f() : Y * bool = {
    var y;
    y <$ dY;
    return (y, mem Mem.used y);
  }
}.

(* Permutation: fresh outputs sampled WITHOUT replacement, written in the  *)
(* "indirect" resampling form (draw once, resample off the image on a      *)
(* collision) so it is syntactically identical to RealO until the bad bit. *)
module IdealO : RawOracle = {
  proc init() : unit = { Mem.t <- empty; Mem.used <- fset0; }
  proc f() : Y * bool = {
    var y, b;
    y <$ dY;
    b <- mem Mem.used y;
    if (b) {
      y <$ dY \ mem Mem.used;
    }
    return (y, b);
  }
}.

(* The bounded-query, input-memoising experiment.  The wrapper             *)
(*  - returns the cached output on a repeated input (no sampling),         *)
(*  - on a fresh input within budget, draws a fresh output via O.f,        *)
(*    records it in t and in the image `used`, counts the fresh query,     *)
(*    and latches the bad flag.                                            *)
module Exp (O : RawOracle) (A : Adv) = {
  module WO : Oracle = {
    var cF  : int
    var bad : bool

    proc init() : unit = {
      bad <- false;
      cF  <- 0;
      O.init();
    }

    proc eval(x : X) : Y = {
      var y, b;
      b <- false;
      y <- oget Mem.t.[x];      (* cached output (witness if x is fresh) *)
      if (x \notin Mem.t /\ cF < q /\ !bad) {
        (y, b) <@ O.f();
        Mem.t.[x]  <- y;
        Mem.used   <- Mem.used `|` fset1 y;
        cF  <- cF + 1;
        bad <- b ? b : bad;
      }
      return y;
    }
  }

  proc main() : bool = {
    var r;
    WO.init();
    r <@ A(WO).run();
    return r;
  }
}.

(* -------------------------------------------------------------------- *)
(* Per-call building blocks.                                              *)
(* -------------------------------------------------------------------- *)

lemma RealO_f_ll : islossless RealO.f.
proof. proc; auto; smt(dY_ll). qed.

(* The two raw samplers agree unless the with-replacement draw is bad. *)
equiv RealO_IdealO_f :
  RealO.f ~ IdealO.f :
  ={Mem.used} /\ card Mem.used{1} < cardY ==>
  !(res{2}.`2) => ={res}.
proof.
proc.
seq 1 1 : (={y, Mem.used} /\ card Mem.used{1} < cardY); first by auto.
sp.
if{2}.
+ conseq (: _ ==> true) => //.
  rnd{2}; skip => /> &2 hlt _.
  apply (dexcepted_ll dY (mem Mem.used{2}) dY_ll).
  have := mu_dY_mem Mem.used{2}; smt(cardY_gt0).
+ skip => /> /#.
qed.

(* The without-replacement sampler flags "bad" with probability the        *)
(* with-replacement draw lands in the current image. *)
phoare IdealO_f_bad (S : Y fset) :
  [ IdealO.f : Mem.used = S ==> res.`2 ] <= ((card S)%r / cardY%r).
proof.
proc.
seq 2 : b ((card S)%r / cardY%r) 1%r _ 0%r (true) => //.
+ wp; rnd; skip => &hr [#] -> /=.
  exact (mu_dY_mem S).
+ hoare; rcondf 1; auto.
qed.

(* -------------------------------------------------------------------- *)
(* The switching bound: adv <= q(q-1) / (2|Y|).                            *)
(* -------------------------------------------------------------------- *)

lemma adv_bound &m (A <: Adv {-Exp, -Mem}) (P : bool -> bool) :
  (forall (O <: Oracle{-A}), islossless O.eval => islossless A(O).run) =>
  Pr[Exp(RealO, A).main() @ &m : P res]
  <= Pr[Exp(IdealO, A).main() @ &m : P res]
     + (q * (q - 1))%r / (2%r * cardY%r).
proof.
move=> A_ll.
have hsum : bigi predT g 0 q = (q * (q - 1))%r / (2%r * cardY%r).
+ have -> : bigi predT g 0 q = bigi predT (fun i => i%r) 0 q / cardY%r.
  + rewrite mulr_suml; apply eq_big_int => i hi.
    by rewrite /g /=.
  rewrite sumidE 1:q_ge0; smt(cardY_gt0).
rewrite -hsum.
apply (ler_trans (Pr[Exp(IdealO, A).main() @ &m :
                     P res \/ (Exp.WO.bad /\ Exp.WO.cF <= q)])).
+ byequiv (: ={glob A} ==>
            (!Exp.WO.bad{2} => ={res}) /\ Exp.WO.cF{2} <= q) => //.
  + proc.
    call (: Exp.WO.bad,
            ={Exp.WO.cF, Exp.WO.bad, Mem.t, Mem.used} /\
            card Mem.used{2} <= Exp.WO.cF{2} /\ 0 <= Exp.WO.cF{2} <= q,
            Exp.WO.cF{2} <= q).
    + proc; sp; if => //.
      wp; call RealO_IdealO_f; auto => /> &1 &2 *.
      smt(fcardU1 fcard_ge0 q_le_card).
    + move=> &2 bad_h; proc; sp; if => //.
      by wp; call RealO_f_ll; auto => /#.
    + move=> _; proc; sp; rcondf 1; [ by auto => /# | by auto ].
    inline *.
    auto => />; smt(fcards0 q_ge0).
  smt().
apply (ler_trans (Pr[Exp(IdealO, A).main() @ &m : P res]
                + Pr[Exp(IdealO, A).main() @ &m : Exp.WO.bad /\ Exp.WO.cF <= q])).
+ by rewrite Pr [mu_or]; smt(ge0_mu).
have mono : forall (a b c : real), b <= c => a + b <= a + c by smt().
apply mono.
fel 1 Exp.WO.cF g q Exp.WO.bad
    [Exp(IdealO, A).WO.eval :
       (x \notin Mem.t /\ Exp.WO.cF < q /\ !Exp.WO.bad)]
    (card Mem.used <= Exp.WO.cF /\ 0 <= Exp.WO.cF) => //.
+ inline *; auto; smt(fcards0).
+ proc; sp 2; if => //; wp; last first.
  + by hoare; auto => /#.
  exists* Exp.WO.cF; elim* => c.
  exists* Mem.used; elim* => S.
  conseq (: _ : ((card S)%r / cardY%r)).
  + move=> /> &hr *; rewrite /g; smt(cardY_gt0 fcard_ge0).
  conseq (: _ ==> b).
  + by move=> /> /#.
  call (IdealO_f_bad S); skip => /> /#.
+ move=> c; proc; sp 2; rcondt 1; first by auto.
  wp; call (_ : true ==> true); first by proc; auto.
  auto; smt(fcardU1 fcard_ge0).
+ move=> b c; proc; sp 2; rcondf 1; first by auto => /#.
  by auto => /#.
qed.
