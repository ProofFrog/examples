(* ==================================================================== *)
(* LazyROTwoSeeded: two-point lazy programming of a random oracle         *)
(*                                                                        *)
(* EasyCrypt proof of the ProofFrog statistical helper game pair in the    *)
(* co-located LazyROTwoSeeded.game (and, with the codomain halves          *)
(* renamed, its structural twin CGLazyROTwoSeeded.game -- both are this    *)
(* one generic theory):                                                    *)
(*                                                                        *)
(*   Honest.Initialize() : sample H; s0, s1 <- D (independent);           *)
(*                         return [s0, s1]                                 *)
(*   Honest.Hash(x)      : return H(x)                                    *)
(*   Lazy.Initialize()   : sample H; s0 <- D; s1 <-uniq[{s0}] D;          *)
(*                         pre-sample y0 = y0_pq||y0_t, y1 = y1_pq||y1_t;  *)
(*                         return [s0, s1]                                 *)
(*   Lazy.Hash(x)        : x==s0 -> y0 ; x==s1 -> y1 ; else H(x)          *)
(*                                                                        *)
(* The advertised bound is 2^-lambda: the ONLY loss is the chance that    *)
(* Honest's two independent seeds collide (s0 = s1); the half-split        *)
(* programming is loss-free.                                               *)
(*                                                                        *)
(* Modeling notes (this version aims for MAXIMAL correspondence to the     *)
(* .game, including Lazy's EAGER Initialize-time pre-sampling).            *)
(*  - The domain D = BitString<lambda> is an abstract finite type `seed`   *)
(*    with the uniform dS; cardS = 2^lambda and the bound is 1/cardS.      *)
(*  - The codomain BitString<KEM_PQ.Nseed + KEM_T.Nseed> is the product    *)
(*    `pqh * th` of its two halves, dR = dpq * dth.  A single draw from a  *)
(*    product distribution IS an independent pair of half-draws, so this   *)
(*    models the loss-free concat/split exactly (the product-of-uniforms /*)
(*    `dlist_add` fact); the half-split needs no extra step.               *)
(*  - H is the game-owned random function, reachable only through Hash,    *)
(*    modeled as a PROM.FullRO (modeling default #2).  Lazy's Initialize    *)
(*    pre-samples the two seed outputs y0, y1 EAGERLY (via H.RO.sample,     *)
(*    i.e. the eager RO that samples a point up front); Honest reads them   *)
(*    lazily.  The eager/lazy gap is discharged by PROM's FullEager.RO_LRO  *)
(*    (eager RO indistinguishable from lazy LRO for any distinguisher),     *)
(*    machine-checking that Lazy's eager pre-sampling equals lazy reads.    *)
(*    Lazy keeps its s0 / s1 Hash branch structure (the programmed values   *)
(*    live at the two seed points of the RO map) to mirror the .game.       *)
(*                                                                        *)
(* Proof shape.  With Honest = MainD(D_H, LRO) (lazy, independent seeds)    *)
(* and Lazy = MainD(D_L, RO) (eager pre-sample, distinct seeds):           *)
(*  1. eager_lazy: MainD(D_L, RO) = MainD(D_L, LRO)   [FullEager.RO_LRO].   *)
(*  2. upto:       Honest <= MainD(D_L, LRO) : (P res \/ collide)           *)
(*                 -- identical-until-bad on the seed collision.           *)
(*  3. coll:       Pr[MainD(D_L, LRO) : collide] <= 1/cardS.               *)
(* ==================================================================== *)

require import AllCore List FSet FMap Distr StdOrder.
(*---*) import RealOrder.
require import Dexcepted.
require (*--*) PROM.

(* The seed domain D = BitString<lambda>, uniform, cardS = 2^lambda. *)
type seed.

clone import MFinite as FinSeed with type t <- seed.

op dS : seed distr = FinSeed.dunifin.
op cardS : int = FinSeed.Support.card.

lemma dS_ll : is_lossless dS.
proof. exact FinSeed.dunifin_ll. qed.

lemma dS1E (x : seed) : mu1 dS x = 1%r / cardS%r.
proof. exact FinSeed.dunifin1E. qed.

lemma cardS_gt0 : 0 < cardS.
proof. exact FinSeed.Support.card_gt0. qed.

(* lambda >= 1, so the seed space has at least two points (needed for the *)
(* without-replacement resample to be lossless). *)
axiom cardS_gt1 : 1 < cardS.

(* The two codomain halves (KEM_PQ.Nseed and KEM_T.Nseed bits); their      *)
(* product is the full output BitString<np+nt>. *)
type pqh.
type th.

op dpq : pqh distr.
op dth : th distr.

axiom dpq_ll : is_lossless dpq.
axiom dth_ll : is_lossless dth.

type rho = pqh * th.

op dR : rho distr = dpq `*` dth.

lemma dR_ll : is_lossless dR.
proof. exact (dprod_ll_auto dpq dth dpq_ll dth_ll). qed.

(* The pair of returned seeds. *)
type spair = seed * seed.

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

module type Adv (O : Hash) = {
  proc distinguish(inp : spair) : bool {O.hash}
}.

(* Shared game state: the two seeds and the collision flag. *)
module Mem = {
  var s0  : seed
  var s1  : seed
  var bad : bool
}.

(* The plain Hash wrapper (Honest): just read the RO. *)
module WrapPlain (G : H.RO) : Hash = {
  proc hash(x : seed) : rho = {
    var r;
    r <@ G.get(x);
    return r;
  }
}.

(* The programmed Hash wrapper (Lazy): the s0 / s1 branch structure of the *)
(* .game; each branch reads the (pre-sampled) RO at the corresponding      *)
(* point, so it is observationally `read H` everywhere. *)
module WrapProg (G : H.RO) : Hash = {
  proc hash(x : seed) : rho = {
    var r;
    if (x = Mem.s0) {
      r <@ G.get(Mem.s0);
    } else {
      if (x = Mem.s1) {
        r <@ G.get(Mem.s1);
      } else {
        r <@ G.get(x);
      }
    }
    return r;
  }
}.

(* Honest distinguisher: two independent seeds, plain Hash, no pre-sample.  *)
(* MainD(D_H(A), LRO) is the Honest game. *)
module D_H (Ad : Adv) (G : H.RO) = {
  proc distinguish(u : unit) : bool = {
    var b;
    Mem.s0  <$ dS;
    Mem.s1  <$ dS;
    Mem.bad <- (Mem.s1 = Mem.s0);   (* ghost on this side *)
    b <@ Ad(WrapPlain(G)).distinguish((Mem.s0, Mem.s1));
    return b;
  }
}.

(* Lazy distinguisher: distinct seeds, then EAGER pre-sample of the two     *)
(* seed outputs (G.sample = the eager RO's up-front draw), programmed Hash.  *)
(* MainD(D_L(A), RO) is the Lazy game (faithful eager pre-sampling). *)
module D_L (Ad : Adv) (G : H.RO) = {
  proc distinguish(u : unit) : bool = {
    var b;
    Mem.s0  <$ dS;
    Mem.s1  <$ dS;
    Mem.bad <- (Mem.s1 = Mem.s0);
    if (Mem.bad) {
      Mem.s1 <$ dS \ (pred1 Mem.s0);
    }
    G.sample(Mem.s0);
    G.sample(Mem.s1);
    b <@ Ad(WrapProg(G)).distinguish((Mem.s0, Mem.s1));
    return b;
  }
}.

section PROOF.

declare module A <: Adv {-Mem, -H.RO, -H.FRO}.

declare axiom A_ll :
  forall (O <: Hash{-A}), islossless O.hash => islossless A(O).distinguish.

(* RO.get is lossless and agrees with itself on equal maps. *)
local equiv get_eq : H.RO.get ~ H.RO.get :
  ={x, H.RO.m} ==> ={res, H.RO.m}.
proof. proc; auto. qed.

local lemma get_ll : islossless H.RO.get.
proof. proc; auto; smt(dR_ll). qed.

(* -------------------------------------------------------------------- *)
(* Step 1: Lazy's eager pre-sampling equals lazy reads (FullEager).        *)
(* -------------------------------------------------------------------- *)

local lemma eager_lazy &m (P : bool -> bool) :
  Pr[H.MainD(D_L(A), H.RO).distinguish() @ &m : P res]
  = Pr[H.MainD(D_L(A), H.LRO).distinguish() @ &m : P res].
proof.
have h := H.FullEager.RO_LRO (D_L(A)) _; first by move=> _; exact dR_ll.
by byequiv h.
qed.

(* -------------------------------------------------------------------- *)
(* Step 2: Honest is identical to the lazy Lazy until the seeds collide.   *)
(* -------------------------------------------------------------------- *)

local lemma upto &m (P : bool -> bool) :
  Pr[H.MainD(D_H(A), H.LRO).distinguish() @ &m : P res]
  <= Pr[H.MainD(D_L(A), H.LRO).distinguish() @ &m : P res \/ Mem.bad].
proof.
byequiv (: ={glob A} ==> (!Mem.bad{2} => ={res}) /\ ={Mem.bad}) => //;
  last by smt().
proc.
inline H.MainD(D_H(A), H.LRO).distinguish H.MainD(D_L(A), H.LRO).distinguish.
inline D_H(A, H.LRO).distinguish D_L(A, H.LRO).distinguish.
wp.
call (: Mem.bad,
        ={H.RO.m, Mem.s0, Mem.s1, Mem.bad},
        ={Mem.bad}).
+ exact A_ll.
+ (* Hash agrees while !bad: plain read vs branched read. *)
  proc.
  if{2}.
  + by wp; call get_eq; auto => /> /#.
  + if{2}.
    + by wp; call get_eq; auto => /> /#.
    + by wp; call get_eq; auto => /> /#.
+ (* WrapPlain (LHS) lossless when bad. *)
  move=> &2 _; proc; call get_ll; auto.
+ (* WrapProg (RHS) lossless when bad. *)
  move=> &1; proc.
  if.
  + by call get_ll; auto.
  if.
  + by call get_ll; auto.
  by call get_ll; auto.
(* init: couple seeds, the RO maps start empty; establish the invariant. *)
inline H.LRO.init H.LRO.sample.
seq 5 5 : (={glob A, H.RO.m, Mem.s0, Mem.s1, Mem.bad}); first by auto.
if{2}.
+ wp; rnd{2}; skip => />.
  smt(dexcepted_ll dS_ll dS1E cardS_gt1 cardS_gt0).
+ auto => />; smt().
qed.

(* -------------------------------------------------------------------- *)
(* Step 3: the collision probability is 1/cardS.                          *)
(* -------------------------------------------------------------------- *)

(* WrapProg never touches the collision flag. *)
local lemma wrapProg_pres : hoare[ WrapProg(H.LRO).hash : !Mem.bad ==> !Mem.bad ].
proof.
proc.
if.
+ by inline H.LRO.get; auto.
if.
+ by inline H.LRO.get; auto.
by inline H.LRO.get; auto.
qed.

local lemma dL_bad :
  phoare[ D_L(A, H.LRO).distinguish : true ==> Mem.bad ] <= (1%r / cardS%r).
proof.
proc.
seq 3 : Mem.bad (1%r / cardS%r) 1%r _ 0%r (true) => //.
+ wp; rnd (pred1 Mem.s0); rnd; skip => /> s0 _.
  smt(dS1E).
+ hoare.
  rcondf 1; first by auto.
  inline H.LRO.sample.
  call (: !Mem.bad); first exact wrapProg_pres.
  auto.
qed.

local lemma coll &m :
  Pr[H.MainD(D_L(A), H.LRO).distinguish() @ &m : Mem.bad] <= 1%r / cardS%r.
proof.
byphoare => //.
proc.
call dL_bad.
inline H.LRO.init; auto.
qed.

(* -------------------------------------------------------------------- *)
(* The advantage bound: adv <= 1/cardS = 2^-lambda.                       *)
(*                                                                        *)
(* MainD(D_H, H.LRO) is the Honest game (lazy RO, independent seeds);      *)
(* MainD(D_L, H.RO) is the Lazy game (eager pre-sample, distinct seeds).   *)
(* -------------------------------------------------------------------- *)

lemma adv_bound &m (P : bool -> bool) :
  Pr[H.MainD(D_H(A), H.LRO).distinguish() @ &m : P res]
  <= Pr[H.MainD(D_L(A), H.RO).distinguish() @ &m : P res] + 1%r / cardS%r.
proof.
apply (ler_trans (Pr[H.MainD(D_L(A), H.LRO).distinguish() @ &m : P res \/ Mem.bad])).
+ exact (upto &m P).
rewrite Pr [mu_or].
have hcoll := coll &m.
have := eager_lazy &m P.
smt(ge0_mu).
qed.

end section PROOF.
