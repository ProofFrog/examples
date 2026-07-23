(* ==================================================================== *)
(* LazyROOneSeeded: one-point lazy programming of a random oracle         *)
(*                                                                        *)
(* EasyCrypt proof of the ProofFrog statistical helper game pair in the    *)
(* co-located LazyROOneSeeded.game (and, with the second codomain half     *)
(* renamed, its structural twin CGLazyROOneSeeded.game -- both are this    *)
(* one generic theory):                                                    *)
(*                                                                        *)
(*   Honest.Initialize() : sample H; s0 <- D; return s0                    *)
(*   Honest.Hash(x)      : return H(x)                                     *)
(*   Lazy.Initialize()   : sample H; s0 <- D; pre-sample                   *)
(*                         y0 = y0_pq||y0_t; return s0                     *)
(*   Lazy.Hash(x)        : x = s0 -> y0 ; else H(x)                        *)
(*                                                                        *)
(* The advertised bound is 0, and what is proved here is an EQUALITY of    *)
(* probabilities, not an inequality: there is exactly ONE programmed       *)
(* point, it is freshly sampled, and H(s0) is reachable only through the   *)
(* Hash oracle, so reprogramming it is a change of variable.  Unlike the   *)
(* two-seeded case (LazyROTwoSeeded.ec) there is no second seed and hence  *)
(* no collision event: the statement carries no query bound and no         *)
(* cardinality hypothesis, and the adversary need not be lossless.         *)
(*                                                                        *)
(* Modeling notes (this version aims for MAXIMAL correspondence to the     *)
(* .game, including Lazy's EAGER Initialize-time pre-sampling).            *)
(*  - The domain D = BitString<lambda> is an abstract type `seed` with an  *)
(*    ARBITRARY distribution dS.  Neither uniformity, nor finiteness, nor  *)
(*    losslessness of dS is used anywhere: the two seeds are coupled by    *)
(*    the identity relation and nothing is conditioned on s0's value.  The *)
(*    statement therefore holds a fortiori for the uniform distribution on *)
(*    BitString<lambda> that the .game actually uses.  (Contrast the       *)
(*    two-seeded theory, which needs `cardS_gt1` to bound a collision.)     *)
(*  - The codomain BitString<KEM_PQ.Nseed + KEM_T.Nseed> is the product    *)
(*    `pqh * th` of its two halves, dR = dpq `*` dth.  A single draw from  *)
(*    a product distribution IS an independent pair of half-draws, so this *)
(*    models the loss-free concat/split of the .game's `y0_pq || y0_t`     *)
(*    exactly; the half-split contributes no term.                         *)
(*  - H is the game-owned random function, reachable only through Hash,    *)
(*    modeled as a PROM.FullRO (modeling default #2).  Lazy's Initialize    *)
(*    pre-samples the programmed output EAGERLY (via H.RO.sample, the      *)
(*    eager RO's up-front draw); Honest reads lazily.  The eager/lazy gap  *)
(*    is discharged by PROM's FullEager.RO_LRO, machine-checking that      *)
(*    Lazy's eager pre-sampling equals lazy reads.  Lazy keeps the .game's *)
(*    `x = s0` Hash branch (the programmed value lives at the seed point   *)
(*    of the RO map), so the branch is observationally `read H` and the    *)
(*    second step below is an unconditional equivalence.                    *)
(*  - Identifying the .game's pre-sampled y0 with the RO's value at s0 is  *)
(*    the one place the model does not copy the .game literally: there,    *)
(*    Lazy carries BOTH y0 and an independent H(s0).  But Lazy answers     *)
(*    Hash(s0) with y0 and H is reachable only through Hash, so H(s0) is   *)
(*    unobservable in Lazy -- the two variables have the same distribution *)
(*    and only one of them is ever read.  Storing y0 at the seed point of  *)
(*    the RO map therefore loses nothing, and is what lets the programmed  *)
(*    branch be an ordinary RO read.                                        *)
(*                                                                        *)
(* Proof shape.  With Honest = MainD(D_H, LRO) and Lazy = MainD(D_L, RO):  *)
(*  1. eager_lazy: MainD(D_L, RO) = MainD(D_L, LRO)   [FullEager.RO_LRO].  *)
(*  2. prog_plain: MainD(D_H, LRO) = MainD(D_L, LRO)  -- the programmed    *)
(*     wrapper's two branches both read the RO at the queried point, and   *)
(*     LRO.sample is a no-op, so the two games are the same program.       *)
(*                                                                        *)
(* Adversary class.  A is quantified over {-Mem, -H.RO, -H.FRO}: it may    *)
(* not touch the game-owned seed (Mem.s0) nor the random function (the RO  *)
(* map, and the eager view H.FRO used by RO_LRO).  This is exactly the     *)
(* .game's "H is reachable only through the Hash oracle, s0 only through   *)
(* Initialize's return value", and it is what soundness needs: an          *)
(* adversary holding H could evaluate it at s0 and distinguish.  It is no  *)
(* tighter than that -- A keeps its own state (the restriction is on those *)
(* three modules only), makes unboundedly many Hash queries, is not        *)
(* required to be lossless, and receives s0 as input -- so the lemma is    *)
(* not vacuous and applies to the seeded SAMEKEY reductions, which are     *)
(* ordinary adversaries carrying their own state and calling Hash.         *)
(* ==================================================================== *)

require import AllCore FMap Distr.
require (*--*) PROM.

(* The seed domain D = BitString<lambda>; arbitrary distribution (see the *)
(* modeling note: nothing about dS is used).                              *)
type seed.

op dS : seed distr.

(* The two codomain halves (KEM_PQ.Nseed and KEM_T.Nseed bits); their     *)
(* product is the full output BitString<np+nt>.                           *)
type pqh.
type th.

op dpq : pqh distr.
op dth : th distr.

(* The ONLY axioms of this development: the two halves are lossless.      *)
(* Needed solely by FullEager.RO_LRO (eager sampling must terminate); the *)
(* uniform distribution on a bit string discharges both in any            *)
(* instantiation.  No cardinality hypothesis is needed here -- there is    *)
(* no collision probability to bound.                                     *)
axiom dpq_ll : is_lossless dpq.
axiom dth_ll : is_lossless dth.

type rho = pqh * th.

op dR : rho distr = dpq `*` dth.

lemma dR_ll : is_lossless dR.
proof. exact (dprod_ll_auto dpq dth dpq_ll dth_ll). qed.

(* The random oracle H : seed -> rho. *)
clone import PROM.FullRO as H with
  type in_t    <- seed,
  type out_t   <- rho,
  op   dout    <- (fun (_ : seed) => dR),
  type d_in_t  <- unit,
  type d_out_t <- bool.

(* -------------------------------------------------------------------- *)
(* Module interfaces.                                                     *)
(* -------------------------------------------------------------------- *)

module type Hash = {
  proc hash(x : seed) : rho
}.

(* The adversary learns the seed and distinguishes with Hash access only. *)
module type Adv (O : Hash) = {
  proc distinguish(inp : seed) : bool {O.hash}
}.

(* Game state: the single exposed seed. *)
module Mem = {
  var s0 : seed
}.

(* The plain Hash wrapper (Honest): just read the RO. *)
module WrapPlain (G : H.RO) : Hash = {
  proc hash(x : seed) : rho = {
    var r;
    r <@ G.get(x);
    return r;
  }
}.

(* The programmed Hash wrapper (Lazy): the .game's `x = s0` branch; the   *)
(* branch reads the (pre-sampled) RO at the seed point, so it is          *)
(* observationally `read H` everywhere.                                   *)
module WrapProg (G : H.RO) : Hash = {
  proc hash(x : seed) : rho = {
    var r;
    if (x = Mem.s0) {
      r <@ G.get(Mem.s0);
    } else {
      r <@ G.get(x);
    }
    return r;
  }
}.

(* Honest distinguisher: sample the seed, plain Hash, no pre-sample.      *)
(* MainD(D_H(A), LRO) is the Honest game.  (D_H never calls G.sample, so  *)
(* MainD(D_H(A), RO) is the same program -- the choice is immaterial.)     *)
module D_H (Ad : Adv) (G : H.RO) = {
  proc distinguish(u : unit) : bool = {
    var b;
    Mem.s0 <$ dS;
    b <@ Ad(WrapPlain(G)).distinguish(Mem.s0);
    return b;
  }
}.

(* Lazy distinguisher: sample the seed, then EAGERLY pre-sample the seed  *)
(* output (G.sample = the eager RO's up-front draw), programmed Hash.     *)
(* MainD(D_L(A), RO) is the Lazy game (faithful eager pre-sampling).      *)
module D_L (Ad : Adv) (G : H.RO) = {
  proc distinguish(u : unit) : bool = {
    var b;
    Mem.s0 <$ dS;
    G.sample(Mem.s0);
    b <@ Ad(WrapProg(G)).distinguish(Mem.s0);
    return b;
  }
}.

section PROOF.

declare module A <: Adv {-Mem, -H.RO, -H.FRO}.

(* RO.get agrees with itself on equal maps and equal arguments. *)
local equiv get_eq : H.RO.get ~ H.RO.get :
  ={x, H.RO.m} ==> ={res, H.RO.m}.
proof. proc; auto. qed.

(* -------------------------------------------------------------------- *)
(* Step 1: Lazy's eager pre-sampling equals lazy reads (FullEager).       *)
(* -------------------------------------------------------------------- *)

local lemma eager_lazy &m (P : bool -> bool) :
  Pr[H.MainD(D_L(A), H.RO).distinguish() @ &m : P res]
  = Pr[H.MainD(D_L(A), H.LRO).distinguish() @ &m : P res].
proof.
have h := H.FullEager.RO_LRO (D_L(A)) _; first by move=> _; exact dR_ll.
by byequiv h.
qed.

(* -------------------------------------------------------------------- *)
(* Step 2: with a lazy RO the programmed game IS the honest game.        *)
(* -------------------------------------------------------------------- *)

local lemma prog_plain &m (P : bool -> bool) :
  Pr[H.MainD(D_H(A), H.LRO).distinguish() @ &m : P res]
  = Pr[H.MainD(D_L(A), H.LRO).distinguish() @ &m : P res].
proof.
byequiv (: ={glob A} ==> ={res}) => //.
proc.
inline D_H(A, H.LRO).distinguish D_L(A, H.LRO).distinguish.
(* Lazy's eager pre-sample is a no-op once the RO is lazy. *)
inline{2} H.LRO.sample.
wp.
call (: ={H.RO.m, Mem.s0}).
+ (* Hash agrees: both branches of the programmed wrapper read the RO at *)
  (* the queried point (in the taken branch, x{2} = Mem.s0{2}).           *)
  proc.
  if{2}.
  + by call get_eq; auto.
  + by call get_eq; auto.
(* init: the RO map starts empty and the seeds are coupled. *)
by inline *; auto.
qed.

(* -------------------------------------------------------------------- *)
(* The advantage: exactly 0 -- the two games are perfectly               *)
(* indistinguishable, for every predicate P on the adversary's output.   *)
(*                                                                        *)
(* MainD(D_H, H.LRO) is the Honest game (plain reads, no pre-sample);     *)
(* MainD(D_L, H.RO) is the Lazy game (eager pre-sample at the seed point, *)
(* programmed Hash).                                                      *)
(* -------------------------------------------------------------------- *)

lemma adv_bound &m (P : bool -> bool) :
  Pr[H.MainD(D_H(A), H.LRO).distinguish() @ &m : P res]
  = Pr[H.MainD(D_L(A), H.RO).distinguish() @ &m : P res].
proof. by rewrite (prog_plain &m P) -(eager_lazy &m P). qed.

end section PROOF.
