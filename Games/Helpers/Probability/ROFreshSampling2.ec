(* ==================================================================== *)
(* ROFreshSampling2: the 2-slot tuple variant of ROFreshSampling.         *)
(*                                                                        *)
(* EasyCrypt proof of the ProofFrog statistical helper game pair in the    *)
(* co-located ROFreshSampling2.game.  The game owns H : [D0,D1] -> R and   *)
(* exposes it through Hash; for each slot J, Real.ChallengeJ takes the     *)
(* OTHER coordinate, samples a HIDDEN fresh slot-J value, and returns the  *)
(* hash; Ideal.ChallengeJ returns an independent uniform bitstring.        *)
(*                                                                        *)
(* The advertised bound is (q_chal^2 + q_chal*q_hash) / min_J |DJ|; we     *)
(* prove the slightly tighter                                              *)
(*                                                                        *)
(*   adv <= qC*qH/cardMin + qC*(qC-1)/(2*cardMin),  cardMin = min |D0||D1|.*)
(*                                                                        *)
(* This is an instantiation of the generic engine ROFreshSamplingTuple.ec  *)
(* (see that file for the full proof).  All that is game-specific is the   *)
(* shape of the challenge point: ChallengeJ forms a tuple from the         *)
(* caller's context and the fresh slot-J coordinate, captured by the op    *)
(* `mk2` and the context datatype `ctx2`.  The only mathematical           *)
(* obligation discharged here is `mk_coll`: a freshly-formed challenge     *)
(* point hits any set s with probability <= |s|/cardMin, because matching  *)
(* s forces the hidden slot-J coordinate (uniform on D_J, card >=          *)
(* cardMin).                                                               *)
(*                                                                        *)
(* The two named challenge oracles of the .game are bridged to the         *)
(* engine's single dispatch oracle `chal(c : ctx2)` via the injections     *)
(* C0/C1 (Challenge0 t1 = chal (C0 t1), Challenge1 t0 = chal (C1 t0)).      *)
(* ==================================================================== *)

require import AllCore List FSet Distr StdOrder StdBigop.
(*---*) import RealOrder.
require import Mu_mem.
require ROFreshSamplingTuple.

(* The two finite slot domains, with their uniform distributions. *)
type D0, D1.

clone MFinite as F0 with type t <- D0.
clone MFinite as F1 with type t <- D1.

op dD0 : D0 distr = F0.dunifin.
op dD1 : D1 distr = F1.dunifin.
op cardD0 : int = F0.Support.card.
op cardD1 : int = F1.Support.card.

lemma dD0_ll : is_lossless dD0. proof. exact F0.dunifin_ll. qed.
lemma dD1_ll : is_lossless dD1. proof. exact F1.dunifin_ll. qed.
lemma cardD0_gt0 : 0 < cardD0. proof. exact F0.Support.card_gt0. qed.
lemma cardD1_gt0 : 0 < cardD1. proof. exact F1.Support.card_gt0. qed.

lemma mu_dD0_mem (X : D0 fset) : mu dD0 (mem X) <= (card X)%r / cardD0%r.
proof.
have -> : (card X)%r / cardD0%r = (card X)%r * (1%r / cardD0%r) by smt().
apply (mu_mem_le X dD0 (1%r / cardD0%r)).
by move=> x _; rewrite /dD0 F0.dunifin1E.
qed.

lemma mu_dD1_mem (X : D1 fset) : mu dD1 (mem X) <= (card X)%r / cardD1%r.
proof.
have -> : (card X)%r / cardD1%r = (card X)%r * (1%r / cardD1%r) by smt().
apply (mu_mem_le X dD1 (1%r / cardD1%r)).
by move=> x _; rewrite /dD1 F1.dunifin1E.
qed.

(* The full tuple carrier distribution and the smallest slot cardinality. *)
op dT2 : (D0 * D1) distr = dD0 `*` dD1.
op cardMin2 : int = min cardD0 cardD1.

lemma cardMin2_gt0 : 0 < cardMin2.
proof. rewrite /cardMin2; smt(cardD0_gt0 cardD1_gt0). qed.

(* The challenge context: which slot is challenged, with the caller's
   other coordinate. *)
type ctx2 = [ C0 of D1 | C1 of D0 ].

(* Form the challenge point: put the fresh slot-J coordinate (from the
   carrier fv) into slot J, the caller's coordinate elsewhere. *)
op mk2 (c : ctx2) (fv : D0 * D1) : D0 * D1 =
  with c = C0 t1 => (fv.`1, t1)
  with c = C1 t0 => (t0, fv.`2).

(* ----- The mk_coll obligation, via a generic per-slot bound. ----- *)

(* A fresh challenge point hits s with probability <= |s|/cardMin when
   its formation factors through a slot projection whose marginal is the
   slot's uniform distribution. *)
lemma slot_bound ['tj] (dj : 'tj distr) (cardj : int)
                       (proj : D0 * D1 -> 'tj) (c : ctx2)
                       (s : (D0 * D1) fset) :
  0 < cardj => cardMin2 <= cardj =>
  (forall (X : 'tj fset), mu dj (mem X) <= (card X)%r / cardj%r) =>
  mu dT2 (fun fv => proj fv \in image proj s)
    = mu dj (mem (image proj s)) =>
  (forall fv, proj (mk2 c fv) = proj fv) =>
  mu dT2 (fun fv => mk2 c fv \in s) <= (card s)%r / cardMin2%r.
proof.
move=> hcj hcm hmem hmarg hpr.
apply (ler_trans (mu dT2 (fun fv => proj fv \in image proj s))).
+ apply mu_sub => fv /=; rewrite -(hpr fv) => hin.
  by apply mem_image.
rewrite hmarg.
apply (ler_trans ((card (image proj s))%r / cardj%r)); first exact hmem.
have h1 := fcard_image_leq proj s.
have h2 := fcard_ge0 s.
smt(le_fromint).
qed.

lemma mk_coll2 (c : ctx2) (s : (D0 * D1) fset) :
  mu dT2 (fun fv => mk2 c fv \in s) <= (card s)%r / cardMin2%r.
proof.
case c => [t1 | t0].
+ apply (slot_bound dD0 cardD0 (fun (p : D0 * D1) => p.`1) (C0 t1) s) => //.
  + exact cardD0_gt0.
  + rewrite /cardMin2; smt().
  + exact mu_dD0_mem.
  + rewrite /dT2 (dprodEl dD0 dD1 (mem (image (fun (p : D0 * D1) => p.`1) s))).
    by rewrite dD1_ll.
+ apply (slot_bound dD1 cardD1 (fun (p : D0 * D1) => p.`2) (C1 t0) s) => //.
  + exact cardD1_gt0.
  + rewrite /cardMin2; smt().
  + exact mu_dD1_mem.
  + rewrite /dT2 (dprodEr dD0 dD1 (mem (image (fun (p : D0 * D1) => p.`2) s))).
    by rewrite dD0_ll.
qed.

(* -------------------------------------------------------------------- *)
(* Instantiate the generic engine.                                        *)
(* -------------------------------------------------------------------- *)

clone ROFreshSamplingTuple as E with
  type T       <- D0 * D1,
  type ctx     <- ctx2,
  op   dT      <- dT2,
  op   mk      <- mk2,
  op   cardMin <- cardMin2
  proof dT_ll, cardMin_gt0, mk_coll.
realize dT_ll. by rewrite /dT2 dprod_ll_auto 1:dD0_ll dD1_ll. qed.
realize cardMin_gt0. exact cardMin2_gt0. qed.
realize mk_coll. exact mk_coll2. qed.

(* -------------------------------------------------------------------- *)
(* The named-oracle game: bridge the .game's two Challenge oracles to     *)
(* the engine's single dispatch oracle.                                   *)
(* -------------------------------------------------------------------- *)

module type OraclesN = {
  proc hash(x : D0 * D1) : E.R
  proc chal0(t1 : D1) : E.R
  proc chal1(t0 : D0) : E.R
}.

module type AdvN (O : OraclesN) = {
  proc run() : bool { O.hash, O.chal0, O.chal1 }
}.

(* Adapt the engine's dispatch oracle into the named interface:
   Challenge0 t1 = chal (C0 t1), Challenge1 t0 = chal (C1 t0). *)
module AdW (O : E.Oracles) : OraclesN = {
  proc hash = O.hash
  proc chal0(t1 : D1) : E.R = { var r; r <@ O.chal(C0 t1); return r; }
  proc chal1(t0 : D0) : E.R = { var r; r <@ O.chal(C1 t0); return r; }
}.

module Wrap (AN : AdvN) (O : E.Oracles) = {
  proc run() : bool = {
    var b;
    b <@ AN(AdW(O)).run();
    return b;
  }
}.

lemma adv_bound2
  (AN <: AdvN {-E.Mem, -E.Exp, -E.VI.RO, -E.VI.FRO}) &m (P : bool -> bool) :
  (forall (O <: OraclesN {-AN}),
     islossless O.hash => islossless O.chal0 => islossless O.chal1 =>
     islossless AN(O).run) =>
  Pr[E.Exp(E.RealO, Wrap(AN)).main() @ &m : P res]
  <= Pr[E.Exp(E.IdealO, Wrap(AN)).main() @ &m : P res]
     + (E.qC * E.qH)%r / cardMin2%r
     + (E.qC * (E.qC - 1))%r / (2%r * cardMin2%r).
proof.
move=> AN_ll.
apply (E.adv_bound (Wrap(AN)) _ &m P).
move=> O hh hc.
proc.
call (AN_ll (AdW(O)) hh _ _).
+ proc; call hc; auto.
+ proc; call hc; auto.
auto.
qed.
