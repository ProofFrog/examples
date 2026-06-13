(* ==================================================================== *)
(* ROFreshSampling3: the 3-slot tuple variant of ROFreshSampling.         *)
(*                                                                        *)
(* EasyCrypt proof of the ProofFrog statistical helper game pair in the    *)
(* co-located ROFreshSampling3.game, an instantiation of the generic      *)
(* engine ROFreshSamplingTuple.ec (see that file for the full proof).      *)
(*                                                                        *)
(*   adv <= qC*qH/cardMin + qC*(qC-1)/(2*cardMin),                        *)
(*       cardMin = min(|D0|,|D1|,|D2|).                                    *)
(*                                                                        *)
(* Modeling note: the 3-component hash domain [D0,D1,D2] is represented    *)
(* as the right-nested pair type D0 * (D1 * D2) so the carrier            *)
(* distribution is the binary product dD0 `*` (dD1 `*` dD2) and the slot  *)
(* marginals are clean dprodEl/dprodEr extractions.  The only             *)
(* mathematical obligation discharged here is mk_coll (per slot): a       *)
(* freshly-formed challenge point hits any set s with probability         *)
(* <= |s|/cardMin, because matching s forces the hidden slot-J coordinate *)
(* (uniform on D_J, card >= cardMin).                                     *)
(*                                                                        *)
(* The three named challenge oracles of the .game are bridged to the      *)
(* engine's single dispatch oracle chal(c : ctx3) via the injections      *)
(* C0/C1/C2 (ChallengeJ args = chal (CJ args)).                           *)
(* ==================================================================== *)

require import AllCore List FSet Distr StdOrder StdBigop.
(*---*) import RealOrder.
require import Mu_mem.
require ROFreshSamplingTuple.

type D0, D1, D2.

clone MFinite as F0 with type t <- D0.
clone MFinite as F1 with type t <- D1.
clone MFinite as F2 with type t <- D2.

op dD0 : D0 distr = F0.dunifin.
op dD1 : D1 distr = F1.dunifin.
op dD2 : D2 distr = F2.dunifin.
op cardD0 : int = F0.Support.card.
op cardD1 : int = F1.Support.card.
op cardD2 : int = F2.Support.card.

lemma dD0_ll : is_lossless dD0. proof. exact F0.dunifin_ll. qed.
lemma dD1_ll : is_lossless dD1. proof. exact F1.dunifin_ll. qed.
lemma dD2_ll : is_lossless dD2. proof. exact F2.dunifin_ll. qed.
lemma cardD0_gt0 : 0 < cardD0. proof. exact F0.Support.card_gt0. qed.
lemma cardD1_gt0 : 0 < cardD1. proof. exact F1.Support.card_gt0. qed.
lemma cardD2_gt0 : 0 < cardD2. proof. exact F2.Support.card_gt0. qed.

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

lemma mu_dD2_mem (X : D2 fset) : mu dD2 (mem X) <= (card X)%r / cardD2%r.
proof.
have -> : (card X)%r / cardD2%r = (card X)%r * (1%r / cardD2%r) by smt().
apply (mu_mem_le X dD2 (1%r / cardD2%r)).
by move=> x _; rewrite /dD2 F2.dunifin1E.
qed.

(* T = D0 * (D1 * D2). *)
op dT3 : (D0 * (D1 * D2)) distr = dD0 `*` (dD1 `*` dD2).
op cardMin3 : int = min cardD0 (min cardD1 cardD2).

lemma cardMin3_gt0 : 0 < cardMin3.
proof. rewrite /cardMin3; smt(cardD0_gt0 cardD1_gt0 cardD2_gt0). qed.

(* Context: which slot is challenged, with the caller's other coords. *)
type ctx3 = [ C0 of (D1 * D2) | C1 of (D0 * D2) | C2 of (D0 * D1) ].

op mk3 (c : ctx3) (fv : D0 * (D1 * D2)) : D0 * (D1 * D2) =
  with c = C0 t => (fv.`1, t)
  with c = C1 t => (t.`1, (fv.`2.`1, t.`2))
  with c = C2 t => (t.`1, (t.`2, fv.`2.`2)).

lemma slot_bound ['tj] (dj : 'tj distr) (cardj : int)
                       (proj : D0 * (D1 * D2) -> 'tj) (c : ctx3)
                       (s : (D0 * (D1 * D2)) fset) :
  0 < cardj => cardMin3 <= cardj =>
  (forall (X : 'tj fset), mu dj (mem X) <= (card X)%r / cardj%r) =>
  mu dT3 (fun fv => proj fv \in image proj s)
    = mu dj (mem (image proj s)) =>
  (forall fv, proj (mk3 c fv) = proj fv) =>
  mu dT3 (fun fv => mk3 c fv \in s) <= (card s)%r / cardMin3%r.
proof.
move=> hcj hcm hmem hmarg hpr.
apply (ler_trans (mu dT3 (fun fv => proj fv \in image proj s))).
+ apply mu_sub => fv /=; rewrite -(hpr fv) => hin.
  by apply mem_image.
rewrite hmarg.
apply (ler_trans ((card (image proj s))%r / cardj%r)); first exact hmem.
have h1 := fcard_image_leq proj s.
have h2 := fcard_ge0 s.
smt(le_fromint).
qed.

lemma mk_coll3 (c : ctx3) (s : (D0 * (D1 * D2)) fset) :
  mu dT3 (fun fv => mk3 c fv \in s) <= (card s)%r / cardMin3%r.
proof.
case c => t.
+ apply (slot_bound dD0 cardD0 (fun (p : D0 * (D1 * D2)) => p.`1) (C0 t) s) => //.
  + exact cardD0_gt0.
  + rewrite /cardMin3; smt().
  + exact mu_dD0_mem.
  + rewrite /dT3 (dprodEl dD0 (dD1 `*` dD2)
            (mem (image (fun (p : D0 * (D1 * D2)) => p.`1) s))).
    by rewrite weight_dprod dD1_ll dD2_ll.
+ apply (slot_bound dD1 cardD1 (fun (p : D0 * (D1 * D2)) => p.`2.`1) (C1 t) s) => //.
  + exact cardD1_gt0.
  + rewrite /cardMin3; smt().
  + exact mu_dD1_mem.
  + rewrite /dT3 (dprodEr dD0 (dD1 `*` dD2)
            (fun (r : D1 * D2) => r.`1 \in image (fun (p : D0 * (D1 * D2)) => p.`2.`1) s)).
    rewrite (dprodEl dD1 dD2
            (mem (image (fun (p : D0 * (D1 * D2)) => p.`2.`1) s))).
    by rewrite dD2_ll dD0_ll.
+ apply (slot_bound dD2 cardD2 (fun (p : D0 * (D1 * D2)) => p.`2.`2) (C2 t) s) => //.
  + exact cardD2_gt0.
  + rewrite /cardMin3; smt().
  + exact mu_dD2_mem.
  + rewrite /dT3 (dprodEr dD0 (dD1 `*` dD2)
            (fun (r : D1 * D2) => r.`2 \in image (fun (p : D0 * (D1 * D2)) => p.`2.`2) s)).
    rewrite (dprodEr dD1 dD2
            (mem (image (fun (p : D0 * (D1 * D2)) => p.`2.`2) s))).
    by rewrite dD1_ll dD0_ll.
qed.

(* -------------------------------------------------------------------- *)
(* Instantiate the generic engine.                                        *)
(* -------------------------------------------------------------------- *)

clone ROFreshSamplingTuple as E with
  type T       <- D0 * (D1 * D2),
  type ctx     <- ctx3,
  op   dT      <- dT3,
  op   mk      <- mk3,
  op   cardMin <- cardMin3
  proof dT_ll, cardMin_gt0, mk_coll.
realize dT_ll.
by rewrite /dT3 dprod_ll_auto 1:dD0_ll dprod_ll_auto 1:dD1_ll dD2_ll.
qed.
realize cardMin_gt0. exact cardMin3_gt0. qed.
realize mk_coll. exact mk_coll3. qed.

(* -------------------------------------------------------------------- *)
(* The named-oracle game.                                                 *)
(* -------------------------------------------------------------------- *)

module type OraclesN = {
  proc hash(x : D0 * (D1 * D2)) : E.R
  proc chal0(t1 : D1, t2 : D2) : E.R
  proc chal1(t0 : D0, t2 : D2) : E.R
  proc chal2(t0 : D0, t1 : D1) : E.R
}.

module type AdvN (O : OraclesN) = {
  proc run() : bool { O.hash, O.chal0, O.chal1, O.chal2 }
}.

module AdW (O : E.Oracles) : OraclesN = {
  proc hash = O.hash
  proc chal0(t1 : D1, t2 : D2) : E.R = { var r; r <@ O.chal(C0 (t1, t2)); return r; }
  proc chal1(t0 : D0, t2 : D2) : E.R = { var r; r <@ O.chal(C1 (t0, t2)); return r; }
  proc chal2(t0 : D0, t1 : D1) : E.R = { var r; r <@ O.chal(C2 (t0, t1)); return r; }
}.

module Wrap (AN : AdvN) (O : E.Oracles) = {
  proc run() : bool = {
    var b;
    b <@ AN(AdW(O)).run();
    return b;
  }
}.

lemma adv_bound3
  (AN <: AdvN {-E.Mem, -E.Exp, -E.VI.RO, -E.VI.FRO}) &m (P : bool -> bool) :
  (forall (O <: OraclesN {-AN}),
     islossless O.hash => islossless O.chal0 => islossless O.chal1 =>
     islossless O.chal2 => islossless AN(O).run) =>
  Pr[E.Exp(E.RealO, Wrap(AN)).main() @ &m : P res]
  <= Pr[E.Exp(E.IdealO, Wrap(AN)).main() @ &m : P res]
     + (E.qC * E.qH)%r / cardMin3%r
     + (E.qC * (E.qC - 1))%r / (2%r * cardMin3%r).
proof.
move=> AN_ll.
apply (E.adv_bound (Wrap(AN)) _ &m P).
move=> O hh hc.
proc.
call (AN_ll (AdW(O)) hh _ _ _).
+ proc; call hc; auto.
+ proc; call hc; auto.
+ proc; call hc; auto.
auto.
qed.
