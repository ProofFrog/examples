(* ==================================================================== *)
(* SamplingWithoutReplacement: with-replacement vs without-replacement    *)
(*                                                                        *)
(* EasyCrypt proofs of the two surviving ProofFrog "sampling without      *)
(* replacement" statistical helper games:                                 *)
(*                                                                        *)
(*   NonzeroSampling.game   (exclude a fixed element)                      *)
(*       -> lemma adv_bound_const     : adv <= q / |S|                     *)
(*   DistinctSampling.game  (internal birthday bookkeeping)                *)
(*       -> lemma adv_bound_birthday  : adv <= q(q-1) / (2|S|)             *)
(*                                                                        *)
(* Both are corollaries of one generic experiment that compares           *)
(*                                                                        *)
(*   RealS.f(bk)  : v <- S            (uniform, with replacement)          *)
(*   IdealS.f(bk) : v <-uniq[bk] S    (uniform on dS \ mem bk)             *)
(*                                                                        *)
(* parameterized by a per-query cardinality cap `sizeBound : int -> int`  *)
(* that the experiment enforces (`card bk <= sizeBound (query index)`).   *)
(* The generic result is                                                  *)
(*                                                                        *)
(*   adv_bound : adv <= bigi predT (fun k => (sizeBound k)%r / |S|) 0 q    *)
(*             = (sum over the q queries of the per-query cap) / |S|.      *)
(*                                                                        *)
(* and the two games are its specializations:                             *)
(*   - NonzeroSampling : constant cap 1   -> q / |S|                       *)
(*   - DistinctSampling: linear cap k     -> q(q-1)/(2|S|)  (birthday).    *)
(*                                                                        *)
(* WHY THE CAP.  The naive "exclude any caller-supplied set" statement is *)
(* unsound: passing bk = S \ {x} makes IdealS deterministic while RealS   *)
(* stays uniform, giving advantage ~ 1.  The cap makes the bound honest   *)
(* and unconditional; the two surviving games each fix the cap internally *)
(* (NonzeroSampling excludes one fixed element; DistinctSampling tracks   *)
(* its own growing set), so neither exposes a misusable caller set.       *)
(*                                                                        *)
(* HISTORY.  The generic `adv_bound` once backed a caller-supplied-set    *)
(* `UniqueSampling.game`; that game was removed (2026-06-12, af2e2ca) as  *)
(* misusable.  `adv_bound` is retained here as the shared proof engine    *)
(* the two corollaries specialize, not because any game uses the general  *)
(* (caller-supplied-set) form.                                            *)
(* ==================================================================== *)

require import AllCore List FSet Distr StdOrder StdBigop.
(*---*) import RealOrder Bigreal BRA.
require import Dexcepted Mu_mem.
require import FelTactic.

(* The finite sample space S, with its uniform distribution dS. *)
type S.

clone import MFinite as FinS with type t <- S.

op dS : S distr = FinS.dunifin.
op cardS : int = FinS.Support.card.

lemma dS_ll : is_lossless dS.
proof. exact FinS.dunifin_ll. qed.

lemma dS_uni : is_uniform dS.
proof. exact FinS.dunifin_uni. qed.

lemma dS1E (x : S) : mu1 dS x = 1%r / cardS%r.
proof. exact FinS.dunifin1E. qed.

lemma cardS_gt0 : 0 < cardS.
proof. exact FinS.Support.card_gt0. qed.

(* Key per-query measure: the probability a uniform sample lands in a set. *)
lemma mu_dS_mem (X : S fset) : mu dS (mem X) <= (card X)%r / cardS%r.
proof.
have -> : (card X)%r / cardS%r = (card X)%r * (1%r / cardS%r) by smt().
apply (mu_mem_le X dS (1%r / cardS%r)).
move=> x _; rewrite dS1E //.
qed.

(* -------------------------------------------------------------------- *)
(* Experiment parameters.                                                 *)
(* -------------------------------------------------------------------- *)

(* maximum number of queries the adversary may make *)
op q : { int | 0 <= q } as q_ge0.

(* per-query cardinality cap: at the k-th query (0-indexed) the caller    *)
(* may supply a bookkeeping set of size at most `sizeBound k`.            *)
op sizeBound : int -> int.

axiom sizeBound_ge0 k : 0 <= sizeBound k.

(* For the bound to be non-vacuous (and the without-replacement sampler   *)
(* lossless) we need the excluded set to be a proper subset of S.         *)
axiom sizeBound_lt_card k : 0 <= k < q => sizeBound k < cardS.

(* per-query bad-event rate *)
op g (k : int) : real = (sizeBound k)%r / cardS%r.

lemma g_ge0 k : 0%r <= g k.
proof. rewrite /g; smt(sizeBound_ge0 cardS_gt0). qed.

(* -------------------------------------------------------------------- *)
(* Module interfaces.                                                     *)
(* -------------------------------------------------------------------- *)

(* What the adversary sees: a sampling oracle taking the caller's set. *)
module type Sampler = {
  proc samp(bk : S fset) : S
}.

module type Adv (O : Sampler) = {
  proc run() : bool { O.samp }
}.

(* The "raw" sampler the experiment wraps: it returns the sampled value   *)
(* together with the bad bit (did the *with-replacement* draw land in bk).*)
module type RawSampler = {
  proc init() : unit
  proc f(bk : S fset) : S * bool
}.

(* Real world: sampling with replacement. The bad bit records whether the *)
(* draw collided with the excluded set. *)
module RealS : RawSampler = {
  proc init() : unit = { }
  proc f(bk : S fset) : S * bool = {
    var v;
    v <$ dS;
    return (v, mem bk v);
  }
}.

(* Ideal world: sampling without replacement, written in "indirect" form  *)
(* (draw once from dS, resample from dS \ bk on collision) so that it is   *)
(* syntactically identical to RealS until the bad bit is set. *)
module IdealS : RawSampler = {
  proc init() : unit = { }
  proc f(bk : S fset) : S * bool = {
    var v, b;
    v <$ dS;
    b <- mem bk v;
    if (b) {
      v <$ dS \ mem bk;
    }
    return (v, b);
  }
}.

(* The bounded-query experiment.  The wrapper                              *)
(*  - counts queries (cO),                                                 *)
(*  - latches the bad flag,                                                *)
(*  - enforces the per-query cardinality discipline card bk <= sizeBound cO*)
(*    (out-of-discipline queries are no-ops, identical in both worlds).    *)
module Exp (O : RawSampler) (A : Adv) = {
  module WO : Sampler = {
    var cO : int
    var bad : bool

    proc init() : unit = {
      bad <- false;
      cO  <- 0;
      O.init();
    }

    proc samp(bk : S fset) : S = {
      var v, b;
      v <- witness;
      b <- false;
      if (cO < q /\ !bad /\ card bk <= sizeBound cO) {
        (v, b) <@ O.f(bk);
        cO  <- cO + 1;
        bad <- b ? b : bad;
      }
      return v;
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

lemma RealS_f_ll : islossless RealS.f.
proof. proc; auto; smt(dS_ll). qed.

(* The two raw samplers agree unless the with-replacement draw is bad. *)
equiv RealS_IdealS_f :
  RealS.f ~ IdealS.f :
  ={bk} /\ card bk{1} < cardS ==>
  !(res{2}.`2) => ={res}.
proof.
proc.
seq 1 1 : (={v, bk} /\ card bk{1} < cardS); first by auto.
sp.
if{2}.
+ conseq (: _ ==> true) => //.
  rnd{2}; skip => /> &2 hlt _.
  apply (dexcepted_ll dS (mem bk{2}) dS_ll).
  have := mu_dS_mem bk{2}; smt(cardS_gt0).
+ skip => /> /#.
qed.

(* The without-replacement sampler flags "bad" with probability the       *)
(* with-replacement draw lands in the excluded set. *)
phoare IdealS_f_bad (X : S fset) :
  [ IdealS.f : bk = X /\ card X < cardS ==> res.`2 ] <= ((card X)%r / cardS%r).
proof.
proc.
seq 2 : b ((card X)%r / cardS%r) 1%r _ 0%r (true) => //.
+ wp; rnd; skip => &hr [#] -> _ /=.
  exact (mu_dS_mem X).
+ hoare; rcondf 1; auto.
qed.

(* -------------------------------------------------------------------- *)
(* Generic advantage bound.                                               *)
(* -------------------------------------------------------------------- *)

lemma adv_bound &m (A <: Adv {-Exp, -RealS, -IdealS}) (P : bool -> bool) :
  (forall (O <: Sampler{-A}), islossless O.samp => islossless A(O).run) =>
  Pr[Exp(RealS, A).main() @ &m : P res]
  <= Pr[Exp(IdealS, A).main() @ &m : P res]
     + bigi predT g 0 q.
proof.
move=> A_ll.
apply (ler_trans (Pr[Exp(IdealS, A).main() @ &m :
                     P res \/ (Exp.WO.bad /\ Exp.WO.cO <= q)])).
+ byequiv (: ={glob A} ==>
            (!Exp.WO.bad{2} => ={res}) /\ Exp.WO.cO{2} <= q) => //.
  + proc.
    call (: Exp.WO.bad,
            ={Exp.WO.cO, Exp.WO.bad} /\ 0 <= Exp.WO.cO{2} <= q,
            Exp.WO.cO{2} <= q).
    + proc; sp; if => //.
      wp; call RealS_IdealS_f; auto => /> &1 &2 *.
      smt(sizeBound_lt_card).
    + move=> &2 bad_h; proc; sp; if => //.
      by wp; call RealS_f_ll; auto => /#.
    + move=> _; proc; sp; rcondf 1; [ by auto=> /# | by auto ].
    inline *.
    auto => />; smt(q_ge0).
  smt().
(* Union bound: split the combined event into P res and the bad event. *)
apply (ler_trans (Pr[Exp(IdealS, A).main() @ &m : P res]
                + Pr[Exp(IdealS, A).main() @ &m : Exp.WO.bad /\ Exp.WO.cO <= q])).
+ by rewrite Pr [mu_or]; smt(ge0_mu).
have mono : forall (a b c : real), b <= c => a + b <= a + c by smt().
apply mono.
(* Bound the bad probability with the failure-event lemma. *)
fel 1 Exp.WO.cO g q Exp.WO.bad
    [Exp(IdealS, A).WO.samp :
       (!Exp.WO.bad /\ Exp.WO.cO < q /\ card bk <= sizeBound Exp.WO.cO)]
    (0 <= Exp.WO.cO) => //.
+ inline *; auto.
+ proc; sp 2; if => //; wp; last first.
  + by hoare; auto => /#.
  exists* Exp.WO.cO; elim* => c.
  exists* bk; elim* => X.
  conseq (: _ : ((card X)%r / cardS%r)).
  + move=> /> &hr *; rewrite /g; smt(cardS_gt0 sizeBound_ge0).
  conseq (: _ ==> b).
  + by move=> /> /#.
  call (IdealS_f_bad X); skip => /> /#.
+ move=> c; proc; sp; rcondt 1; first by auto.
  inline *; auto.
  seq 3 : (c < Exp.WO.cO + 1 /\ 0 <= Exp.WO.cO + 1).
  + by auto; smt().
  by if; auto.
+ move=> b c; proc; sp; rcondf 1; first by auto => /#.
  by auto.
qed.

(* -------------------------------------------------------------------- *)
(* Corollaries matching the two corpus usages.                            *)
(* -------------------------------------------------------------------- *)

(* Constant cap 1 (the {0}-style usage): advantage <= q / |S|. *)
lemma adv_bound_const &m (A <: Adv {-Exp, -RealS, -IdealS}) (P : bool -> bool) :
  (forall k, 0 <= k < q => sizeBound k = 1) =>
  (forall (O <: Sampler{-A}), islossless O.samp => islossless A(O).run) =>
  Pr[Exp(RealS, A).main() @ &m : P res]
  <= Pr[Exp(IdealS, A).main() @ &m : P res]
     + q%r / cardS%r.
proof.
move=> hsz hll.
have E : bigi predT g 0 q = q%r / cardS%r.
+ have -> : bigi predT g 0 q = bigi predT (fun _ => 1%r / cardS%r) 0 q.
  + by apply eq_big_int => i hi; rewrite /g (hsz i hi).
  rewrite sumri_const 1:q_ge0 /=; smt().
rewrite -E; exact (adv_bound &m A P hll).
qed.

(* Linear cap k (the accumulating-bookkeeping usage): the birthday shape   *)
(* advantage <= q(q-1) / (2|S|)  (<= q^2/|S|).                             *)
lemma adv_bound_birthday &m (A <: Adv {-Exp, -RealS, -IdealS}) (P : bool -> bool) :
  (forall k, 0 <= k < q => sizeBound k = k) =>
  (forall (O <: Sampler{-A}), islossless O.samp => islossless A(O).run) =>
  Pr[Exp(RealS, A).main() @ &m : P res]
  <= Pr[Exp(IdealS, A).main() @ &m : P res]
     + (q * (q - 1))%r / (2%r * cardS%r).
proof.
move=> hsz hll.
have E : bigi predT g 0 q = (q * (q - 1))%r / (2%r * cardS%r).
+ have -> : bigi predT g 0 q = bigi predT (fun i => i%r) 0 q / cardS%r.
  + rewrite mulr_suml; apply eq_big_int => i hi.
    by rewrite /g (hsz i hi) /=.
  rewrite sumidE 1:q_ge0; smt(cardS_gt0).
rewrite -E; exact (adv_bound &m A P hll).
qed.
