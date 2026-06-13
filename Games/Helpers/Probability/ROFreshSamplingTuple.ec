(* ==================================================================== *)
(* ROFreshSamplingTuple: generic engine for the tuple-domain variants     *)
(* of ROFreshSampling (the arity 2..5 games).                             *)
(*                                                                        *)
(* This is the shared proof engine that ROFreshSampling2 .. 5 clone.  It  *)
(* generalizes the arity-1 ROFreshSampling.ec from "the challenge point   *)
(* IS a fresh uniform draw" to "the challenge point is formed at call     *)
(* time from adaptive context plus a fresh, input-independent coordinate".*)
(*                                                                        *)
(* Abstract parameters supplied by each instantiation:                    *)
(*   type T        the hash domain (the full tuple [D0,..,D{N-1}])         *)
(*   type ctx      the challenge context (which slot J, plus the other    *)
(*                 N-1 coordinates the caller supplies)                    *)
(*   op   dT       distribution of the fresh coordinate carrier (a full   *)
(*                 fresh tuple; only its challenged slot is used by mk)    *)
(*   op   mk       mk c fv : forms the challenge point from context c and  *)
(*                 the fresh carrier fv                                    *)
(*   op   cardMin  min_J |D_J|, the smallest challenged-slot cardinality   *)
(*   axiom mk_coll the only mathematical content: for every context and   *)
(*                 set s, a freshly-formed challenge point lands in s with *)
(*                 probability <= |s| / cardMin  (because matching s       *)
(*                 forces the hidden slot-J coordinate, uniform on D_J).   *)
(*                                                                        *)
(* The engine proves, for any bounded adversary with qH Hash and qC       *)
(* Challenge queries,                                                      *)
(*                                                                        *)
(*   adv <= qC*qH/cardMin + qC*(qC-1)/(2*cardMin),                        *)
(*                                                                        *)
(* i.e. the advertised (qC^2/2 + qC*qH)/cardMin with the slightly tighter *)
(* birthday constant.                                                     *)
(*                                                                        *)
(* Proof shape (mirrors ROFreshSampling.ec).                              *)
(*  1. Real is identical to an instrumented Ideal (GuessO: forms+logs the  *)
(*     challenge point, answers a fresh y) until BAD = "some challenge     *)
(*     point collides with another challenge point or a Hash query".       *)
(*  2. The instrumented Ideal equals Ideal (the log is dead code).         *)
(*  3. Pr[BAD] is bounded by deferring the (dead) coordinate sampling:     *)
(*     present the fresh carriers as a PROM index-RO, presample them with  *)
(*     FullEager.RO_LRO, drop the now-unread carriers from the run         *)
(*     (the challenge oracle only logs its context), and re-form the       *)
(*     points in a post-run loop where a Birthday-style fel latches BAD    *)
(*     at sampling time with per-step rate (qH+k)/cardMin via mk_coll.     *)
(* ==================================================================== *)

require import AllCore List FSet FMap Distr StdOrder StdBigop.
(*---*) import RealOrder Bigreal BRA.
require import Mu_mem FelTactic.
require (*--*) PROM.

(* The hash domain / point type. *)
type T.

(* The challenge context type (slot tag plus the caller's other slots). *)
type ctx.

(* The fresh-carrier distribution: a full fresh tuple, of which mk uses
   only the challenged slot.  Lossless (each coordinate distribution is). *)
op dT : T distr.

axiom dT_ll : is_lossless dT.

(* Form the challenge point from context and fresh carrier. *)
op mk : ctx -> T -> T.

(* The smallest challenged-slot cardinality. *)
op cardMin : int.

axiom cardMin_gt0 : 0 < cardMin.

(* The sole mathematical content: a freshly-formed challenge point hits
   any fixed set s with probability at most |s| / cardMin, because the
   hit forces the hidden slot-J coordinate, which is uniform on D_J
   (card >= cardMin) and independent of the context. *)
axiom mk_coll (c : ctx) (s : T fset) :
  mu dT (fun fv => mk c fv \in s) <= (card s)%r / cardMin%r.

(* The hash codomain R: any lossless distribution. *)
type R.

op dR : R distr.

axiom dR_ll : is_lossless dR.

(* query budgets *)
op qH : { int | 0 <= qH } as qH_ge0.
op qC : { int | 0 <= qC } as qC_ge0.

(* The PROM random oracle holding the fresh carriers, indexed by the
   challenge counter.  Only proof machinery; the games never expose it. *)
clone PROM.FullRO as VI with
  type in_t    <- int,
  type out_t   <- T,
  op   dout    <- (fun (_ : int) => dT),
  type d_in_t  <- unit,
  type d_out_t <- bool.

(* -------------------------------------------------------------------- *)
(* Module interfaces.                                                     *)
(* -------------------------------------------------------------------- *)

module type Oracles = {
  proc hash(x : T) : R
  proc chal(c : ctx) : R
}.

module type Adv (O : Oracles) = {
  proc run() : bool { O.hash, O.chal }
}.

module type RawG = {
  proc init() : unit
  proc fhash(x : T) : R
  proc fchal(c : ctx) : R
}.

(* Shared game state: the lazy RO map, the challenge-point log (a ghost
   in the ideal worlds), and the context log (used after the run). *)
module Mem = {
  var m    : (T, R) fmap
  var chal : T list
  var ctxl : ctx list
}.

(* Real world: Challenge evaluates the RO at a freshly-formed point.
   Both procs sample unconditionally and store on a miss (PROM get style)
   so that fresh samples couple one-one with the ideal world. *)
module RealO : RawG = {
  proc init() : unit = {
    Mem.m    <- empty;
    Mem.chal <- [];
    Mem.ctxl <- [];
  }

  proc fhash(x : T) : R = {
    var y;
    y <$ dR;
    if (x \notin Mem.m) {
      Mem.m.[x] <- y;
    }
    return oget Mem.m.[x];
  }

  proc fchal(c : ctx) : R = {
    var fv, pt, y;
    fv <$ dT;
    pt <- mk c fv;
    y  <$ dR;
    if (pt \notin Mem.m) {
      Mem.m.[pt] <- y;
    }
    return oget Mem.m.[pt];
  }
}.

(* Ideal world: Challenge returns an independent fresh sample. *)
module IdealO : RawG = {
  proc init = RealO.init

  proc fhash = RealO.fhash

  proc fchal(c : ctx) : R = {
    var y;
    y <$ dR;
    return y;
  }
}.

(* Bridge: ideal answers, but still samples and logs the challenge point. *)
module GuessO : RawG = {
  proc init = RealO.init

  proc fhash = RealO.fhash

  proc fchal(c : ctx) : R = {
    var fv, pt, y;
    fv       <$ dT;
    pt       <- mk c fv;
    Mem.chal <- Mem.chal ++ [pt];
    y        <$ dR;
    return y;
  }
}.

(* The bounded-query experiment. *)
module Exp (O : RawG) (A : Adv) = {
  module WO : Oracles = {
    var cH : int
    var cC : int

    proc init() : unit = {
      cH <- 0;
      cC <- 0;
      O.init();
    }

    proc hash(x : T) : R = {
      var r;
      r <- witness;
      if (cH < qH) {
        r  <@ O.fhash(x);
        cH <- cH + 1;
      }
      return r;
    }

    proc chal(c : ctx) : R = {
      var r;
      r <- witness;
      if (cC < qC) {
        r  <@ O.fchal(c);
        cC <- cC + 1;
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

(* The bad event: a challenge point collides with another challenge
   point or with a hashed point. *)
abbrev bad_ev (chal : T list) (hashed : T fset) : bool =
  !uniq chal \/ has (mem hashed) chal.

(* -------------------------------------------------------------------- *)
(* The advantage bound.                                                   *)
(* -------------------------------------------------------------------- *)

section PROOF.

declare module A <: Adv {-Mem, -Exp, -VI.RO, -VI.FRO}.

declare axiom A_ll :
  forall (O <: Oracles {-A}),
    islossless O.hash => islossless O.chal => islossless A(O).run.

(* Ideal-world oracles with no challenge-point bookkeeping (the
   post-eager games' hash; chal only logs its context). *)
local module CtxO : Oracles = {
  proc hash(x : T) : R = {
    var r, y;
    r <- witness;
    if (Exp.WO.cH < qH) {
      y <$ dR;
      if (x \notin Mem.m) {
        Mem.m.[x] <- y;
      }
      r         <- oget Mem.m.[x];
      Exp.WO.cH <- Exp.WO.cH + 1;
    }
    return r;
  }

  proc chal(c : ctx) : R = {
    var r, y;
    r <- witness;
    if (Exp.WO.cC < qC) {
      Mem.ctxl  <- Mem.ctxl ++ [c];
      y         <$ dR;
      r         <- y;
      Exp.WO.cC <- Exp.WO.cC + 1;
    }
    return r;
  }
}.

(* The PROM distinguisher: like Exp(GuessO, A), but the fresh carriers
   come from the index-RO V; the up-front sample loop is a no-op for LRO
   (lazy = GuessO) and a presampling pass for RO (eager). *)
local module DV (V : VI.RO) = {
  module O : Oracles = {
    proc hash(x : T) : R = {
      var r, y;
      r <- witness;
      if (Exp.WO.cH < qH) {
        y <$ dR;
        if (x \notin Mem.m) {
          Mem.m.[x] <- y;
        }
        r         <- oget Mem.m.[x];
        Exp.WO.cH <- Exp.WO.cH + 1;
      }
      return r;
    }

    proc chal(c : ctx) : R = {
      var r, fv, pt, y;
      r <- witness;
      if (Exp.WO.cC < qC) {
        fv        <@ V.get(Exp.WO.cC);
        pt        <- mk c fv;
        Mem.chal  <- Mem.chal ++ [pt];
        y         <$ dR;
        r         <- y;
        Exp.WO.cC <- Exp.WO.cC + 1;
      }
      return r;
    }
  }

  proc distinguish(du : unit) : bool = {
    var i, r;
    Mem.m     <- empty;
    Mem.chal  <- [];
    Mem.ctxl  <- [];
    Exp.WO.cH <- 0;
    Exp.WO.cC <- 0;
    i <- 0;
    while (i < qC) {
      V.sample(i);
      i <- i + 1;
    }
    r <@ A(O).run();
    return bad_ev Mem.chal (fdom Mem.m);
  }
}.

(* The challenge points formed from the logged contexts and a carrier
   list: qC points, the j-th using context ctxl[j] (witness past the
   adversary's actual challenge count) and carrier cs[j]. *)
op mkpts (ctxl : ctx list) (cs : T list) : T list =
  mkseq (fun j => mk (nth witness ctxl j) (nth witness cs j)) qC.

(* Presampled carriers as a plain list, the run only logs contexts; the
   challenge points are re-formed (mkpts) at the bad-event check. *)
local module G4 = {
  var chalF : T list

  proc main() : bool = {
    var i, r, fv;
    Mem.m     <- empty;
    Mem.chal  <- [];
    Mem.ctxl  <- [];
    Exp.WO.cH <- 0;
    Exp.WO.cC <- 0;
    chalF     <- [];
    i <- 0;
    while (i < qC) {
      fv    <$ dT;
      chalF <- chalF ++ [fv];
      i     <- i + 1;
    }
    r <@ A(CtxO).run();
    return bad_ev (mkpts Mem.ctxl chalF) (fdom Mem.m);
  }
}.

(* Carriers sampled after the run, bad latched at sampling time. *)
local module Smp = {
  var bad : bool

  proc s(c : ctx) : unit = {
    var fv, pt;
    fv       <$ dT;
    pt       <- mk c fv;
    Smp.bad  <- Smp.bad \/ pt \in Mem.chal \/ pt \in fdom Mem.m;
    Mem.chal <- Mem.chal ++ [pt];
  }
}.

local module G3 = {
  proc main() : unit = {
    var i, r;
    Mem.m     <- empty;
    Mem.chal  <- [];
    Mem.ctxl  <- [];
    Exp.WO.cH <- 0;
    Exp.WO.cC <- 0;
    Smp.bad   <- false;
    r <@ A(CtxO).run();
    i <- 0;
    while (i < qC) {
      Smp.s(nth witness Mem.ctxl i);
      i <- i + 1;
    }
  }
}.

(* ------------------------------------------------------------------ *)
(* Step 1: Real is identical to Guess until bad.                        *)
(* ------------------------------------------------------------------ *)

local lemma pr_real_guess &m (P : bool -> bool) :
  Pr[Exp(RealO, A).main() @ &m : P res]
  <= Pr[Exp(GuessO, A).main() @ &m :
          P res \/ bad_ev Mem.chal (fdom Mem.m)].
proof.
byequiv (: ={glob A} ==>
           !(bad_ev Mem.chal (fdom Mem.m)){2} => ={res}) => //;
  last by smt().
proc.
call (: bad_ev Mem.chal (fdom Mem.m),
        ={Exp.WO.cH, Exp.WO.cC} /\
        (forall x, x \in Mem.m{2} => Mem.m{1}.[x] = Mem.m{2}.[x]) /\
        fdom Mem.m{1} = fdom Mem.m{2} `|` oflist Mem.chal{2},
        true).
+ exact A_ll.
+ proc; sp; if => //.
  inline *; auto => /> &1 &2 hnb hval hdom hlt yL hyL.
  split=> [hx2 | hx2].
  + split=> hx1 hnb'.
    + split; first by rewrite !get_set_sameE.
      split; first by smt(get_setE mem_set).
      smt(fdom_set fsetP in_fsetU in_fset1).
    + have hxchal : x{2} \in Mem.chal{2}.
      + smt(mem_fdom in_fsetU mem_oflist).
      have hcontra : has (mem (fdom Mem.m{2}.[x{2} <- yL])) Mem.chal{2}.
      + by rewrite hasP; exists x{2}; smt(mem_fdom mem_set).
      smt().
  + split=> hx1.
    + smt(mem_fdom in_fsetU).
    + by rewrite (hval _ hx2).
+ move=> &2 bad_h; proc; sp; if => //.
  by inline *; auto => />; smt(dR_ll).
+ move=> _; proc; sp; if => //.
  inline *; auto => />; smt(dR_ll cat_uniq has_cat mem_fdom_set hasP hasPn).
+ proc; sp; if => //.
  inline *; auto => /> &1 &2 hnb hval hdom hlt fvL hfvL yL hyL.
  split=> hv1.
  + move=> hnb'.
    split; first by rewrite get_set_sameE.
    split; first by smt(get_setE mem_cat cats1 rcons_uniq mem_fdom hasP).
    rewrite fdom_set hdom fsetP => z.
    by rewrite !in_fsetU in_fset1 mem_oflist mem_oflist mem_cat /#.
  + move=> hnb'.
    have : mk c{2} fvL \in fdom Mem.m{2} \/ mk c{2} fvL \in Mem.chal{2}.
    + smt(mem_fdom in_fsetU mem_oflist).
    case=> [hvm2 | hvch].
    + have : has (mem (fdom Mem.m{2})) (Mem.chal{2} ++ [mk c{2} fvL]).
      + by rewrite hasP; exists (mk c{2} fvL); smt(mem_cat).
      smt().
    + smt(cats1 rcons_uniq).
+ move=> &2 bad_h; proc; sp; if => //.
  by inline *; auto => />; smt(dR_ll dT_ll).
+ move=> _; proc; sp; if => //.
  inline *; auto => />; smt(dT_ll dR_ll cat_uniq has_cat hasP hasPn mem_cat).
inline *; auto => />.
smt(fdom0 in_fsetU in_fset0 mem_oflist fsetP).
qed.

(* ------------------------------------------------------------------ *)
(* Step 2: the challenge log is dead code: Guess = Ideal on outputs.    *)
(* ------------------------------------------------------------------ *)

local lemma pr_guess_ideal &m (P : bool -> bool) :
  Pr[Exp(GuessO, A).main() @ &m : P res]
  = Pr[Exp(IdealO, A).main() @ &m : P res].
proof.
byequiv (: ={glob A} ==> ={res}) => //.
proc.
call (: ={Mem.m, Exp.WO.cH, Exp.WO.cC}).
+ by proc; sp; if => //; inline *; auto.
+ proc; sp; if => //.
  inline *; wp; rnd; wp; rnd{1}; auto => />; smt(dT_ll).
by inline *; auto.
qed.

(* ------------------------------------------------------------------ *)
(* Step 3a: present the fresh carriers as a lazy index-RO.              *)
(* ------------------------------------------------------------------ *)

local lemma pr_guess_lro &m :
  Pr[Exp(GuessO, A).main() @ &m : bad_ev Mem.chal (fdom Mem.m)]
  = Pr[VI.MainD(DV, VI.LRO).distinguish() @ &m : res].
proof.
byequiv (: ={glob A} ==>
           (bad_ev Mem.chal (fdom Mem.m)){1} = res{2}) => //.
proc; inline *; wp.
call (: ={Mem.m, Mem.chal, Exp.WO.cH, Exp.WO.cC} /\
        (forall j, Exp.WO.cC{2} <= j => j \notin VI.RO.m{2})).
+ by proc; sp; if => //; inline *; auto.
+ proc; sp; if => //.
  inline *; sp.
  rcondt{2} 2; first by auto => /> /#.
  by wp; rnd; wp; rnd; auto => />; smt(get_set_sameE mem_set).
while{2} (true) (qC - i{2}); first by move=> _ z; auto => /#.
by auto => /> /#.
qed.

(* ------------------------------------------------------------------ *)
(* Step 3b: lazy to eager via PROM.                                     *)
(* ------------------------------------------------------------------ *)

local lemma pr_lro_ro &m :
  Pr[VI.MainD(DV, VI.LRO).distinguish() @ &m : res]
  = Pr[VI.MainD(DV, VI.RO).distinguish() @ &m : res].
proof.
have h := VI.FullEager.RO_LRO DV _; first by move=> _; exact dT_ll.
by rewrite eq_sym; byequiv h.
qed.

(* ------------------------------------------------------------------ *)
(* Step 3c: the eager index-RO is a presampled list; the run only logs  *)
(* contexts, and the points are re-formed in a post-run loop.           *)
(* ------------------------------------------------------------------ *)

local lemma pr_ro_g4 &m :
  Pr[VI.MainD(DV, VI.RO).distinguish() @ &m : res]
  <= Pr[G4.main() @ &m : res].
proof.
byequiv (: ={glob A} ==> res{1} => res{2}) => //.
proc; inline *; wp.
call (: ={Mem.m, Exp.WO.cH, Exp.WO.cC} /\
        0 <= Exp.WO.cC{2} <= qC /\
        size G4.chalF{2} = qC /\
        size Mem.ctxl{2} = Exp.WO.cC{2} /\
        Mem.chal{1} =
          mkseq (fun j => mk (nth witness Mem.ctxl{2} j)
                             (nth witness G4.chalF{2} j)) Exp.WO.cC{2} /\
        (forall j, 0 <= j < qC =>
           VI.RO.m{1}.[j] = Some (nth witness G4.chalF{2} j))).
+ by proc; sp; if => //; inline *; auto.
+ proc; sp; if => //.
  inline *.
  rcondf{1} 3; first by auto => />; smt(domE).
  wp; rnd; wp; rnd{1}; auto => /> &1 &2 hsz0 hszq hchalF hro hlt.
  split; first by exact dT_ll.
  move=> _ r00 hr00 yL hyL.
  split; first by smt().
  split; first by rewrite size_cat /#.
  have ho : oget VI.RO.m{1}.[size Mem.ctxl{2}]
            = nth witness G4.chalF{2} (size Mem.ctxl{2}).
  + by rewrite (hro (size Mem.ctxl{2})) 1:/# oget_some.
  rewrite (mkseqS _ (size Mem.ctxl{2}) hsz0) /= nth_cat /= ho cats1; congr.
  apply eq_in_mkseq => j [hj0 hjlt] /=.
  by rewrite nth_cat hjlt.
(* couple the presample loops *)
while (={i} /\ 0 <= i{1} <= qC /\
       size G4.chalF{2} = i{2} /\
       (forall j, 0 <= j < i{1} =>
          VI.RO.m{1}.[j] = Some (nth witness G4.chalF{2} j)) /\
       (forall j, i{1} <= j => j \notin VI.RO.m{1})).
+ inline *.
  rcondt{1} 4; first by auto => /> /#.
  auto => />.
  smt(get_setE mem_set size_cat nth_cat cats1 nth_rcons size_rcons).
auto => />.
split; first by smt(mkseq0 qC_ge0).
move=> mL chF hns1 hns2 h0 hle hroL hfresh.
split; first by smt(mkseq0 qC_ge0).
move=> _ _ _ _ mL1 ctxlR mR hcs0 hcsq hro2 hbad.
rewrite /mkpts.
have heq :
  mkseq (fun j => mk (nth witness ctxlR j) (nth witness chF j)) (size ctxlR)
  = take (size ctxlR)
      (mkseq (fun j => mk (nth witness ctxlR j) (nth witness chF j)) qC).
+ by rewrite take_mkseq 1:/#.
move: hbad; rewrite heq => hbad.
case: hbad => [hnu | hh].
+ left.
  have hcat := cat_take_drop (size ctxlR)
    (mkseq (fun j => mk (nth witness ctxlR j) (nth witness chF j)) qC).
  smt(cat_uniq).
+ right; move: hh; rewrite !hasP => -[z] [hz1 hz2].
  by exists z; smt(mem_take).
qed.

(* ------------------------------------------------------------------ *)
(* Step 3d: move the (dead) carrier sampling after the run, latch bad.  *)
(* ------------------------------------------------------------------ *)

local lemma pr_g4_g3 &m :
  Pr[G4.main() @ &m : res]
  <= Pr[G3.main() @ &m : Smp.bad /\ size Mem.chal <= qC].
proof.
byequiv (: ={glob A} ==>
           res{1} => (Smp.bad /\ size Mem.chal <= qC){2}) => //.
proc.
swap{1} [7..8] 1.
(* couple the presample loop {1} with the post-run latch loop {2} *)
while (={i, Mem.m, Mem.ctxl} /\ 0 <= i{1} <= qC /\
       size G4.chalF{1} = i{1} /\
       Mem.chal{2} =
         mkseq (fun j => mk (nth witness Mem.ctxl{2} j)
                            (nth witness G4.chalF{1} j)) i{1} /\
       Smp.bad{2} = bad_ev Mem.chal{2} (fdom Mem.m{2})).
+ inline *; auto => /> &1 &2 hge hle hlt fvL hfvL.
  pose f := fun j => mk (nth witness Mem.ctxl{2} j) (nth witness G4.chalF{1} j).
  have hnthlast :
    nth witness (G4.chalF{1} ++ [fvL]) (size G4.chalF{1}) = fvL.
  + by rewrite nth_cat /=.
  have hmkeq :
    mkseq f (size G4.chalF{1})
    = mkseq (fun j => mk (nth witness Mem.ctxl{2} j)
                         (nth witness (G4.chalF{1} ++ [fvL]) j))
            (size G4.chalF{1}).
  + by apply eq_in_mkseq => j [hj0 hjlt] /=; rewrite nth_cat hjlt.
  split; first by smt().
  split; first by rewrite size_cat /#.
  split.
  + by rewrite (mkseqS _ (size G4.chalF{1}) hge) /= hnthlast -hmkeq cats1.
  by smt(cat_uniq has_cat mem_cat).
wp.
call (: ={Mem.m, Mem.ctxl, Exp.WO.cH, Exp.WO.cC}).
+ by proc; sp; if => //; inline *; auto.
+ by proc; sp; if => //; inline *; auto.
auto => /> ctxl_R m_R.
split; first by smt(mkseq0 qC_ge0).
move=> chalF_L hns _ h0 hle; rewrite /mkpts => hbad.
have hsz : size chalF_L = qC by smt().
rewrite hsz; smt(size_mkseq qC_ge0).
qed.

(* ------------------------------------------------------------------ *)
(* Step 4: the failure-event lemma, Birthday style.                     *)
(* ------------------------------------------------------------------ *)

local lemma pr_g3_fel &m :
  Pr[G3.main() @ &m : Smp.bad /\ size Mem.chal <= qC]
  <= bigi predT (fun k => (qH + k)%r / cardMin%r) 0 qC.
proof.
fel 6 (size Mem.chal)
    (fun k => (qH + k)%r / cardMin%r)
    qC
    Smp.bad
    [Smp.s : true; CtxO.hash : false]
    (card (fdom Mem.m) <= Exp.WO.cH /\ Exp.WO.cH <= qH) => //.
+ (* the init prefix establishes the invariant *)
  by auto => />; smt(fdom0 fcards0 qH_ge0).
+ (* CtxO.hash neutrality: preserves bad and counter, keeps invariant *)
  move=> b c; proc; sp; if => //; inline *; auto => />.
  smt(fdom_set fcardU1 fcard_ge0 size_ge0).
+ (* Smp.s: the per-sample guessing bound *)
  proc; wp; rnd; skip => /> &hr hc0 hcq hnbad hcard hqh.
  apply (ler_trans (mu dT (fun fv =>
           mk c{hr} fv \in (oflist Mem.chal{hr} `|` fdom Mem.m{hr})))).
  + by apply mu_sub => fv; rewrite in_fsetU mem_oflist /#.
  apply (ler_trans ((card (oflist Mem.chal{hr} `|` fdom Mem.m{hr}))%r
                    / cardMin%r)).
  + exact (mk_coll c{hr} (oflist Mem.chal{hr} `|` fdom Mem.m{hr})).
  have hcint : card (oflist Mem.chal{hr} `|` fdom Mem.m{hr})
               <= qH + size Mem.chal{hr}.
  + have h1 := fcardU (oflist Mem.chal{hr}) (fdom Mem.m{hr}).
    have h2 := fcard_oflist Mem.chal{hr}.
    smt(fcard_ge0).
  have hcd := cardMin_gt0.
  smt(le_fromint).
+ (* Smp.s increments the counter *)
  by move=> c; proc; auto => />; smt(size_cat).
qed.

(* ------------------------------------------------------------------ *)
(* Assembly.                                                            *)
(* ------------------------------------------------------------------ *)

lemma adv_bound &m (P : bool -> bool) :
  Pr[Exp(RealO, A).main() @ &m : P res]
  <= Pr[Exp(IdealO, A).main() @ &m : P res]
     + (qC * qH)%r / cardMin%r
     + (qC * (qC - 1))%r / (2%r * cardMin%r).
proof.
have hsum : bigi predT (fun k => (qH + k)%r / cardMin%r) 0 qC
            = (qC * qH)%r / cardMin%r + (qC * (qC - 1))%r / (2%r * cardMin%r).
+ have -> : (fun (k : int) => (qH + k)%r / cardMin%r)
            = (fun (k : int) => qH%r / cardMin%r + k%r * (1%r / cardMin%r)).
  + by apply fun_ext => k; smt().
  rewrite big_split sumri_const 1:qC_ge0 -mulr_suml sumidE 1:qC_ge0.
  smt(cardMin_gt0).
apply (ler_trans (Pr[Exp(GuessO, A).main() @ &m :
                       P res \/ bad_ev Mem.chal (fdom Mem.m)])).
+ exact (pr_real_guess &m P).
apply (ler_trans (Pr[Exp(GuessO, A).main() @ &m : P res]
                + Pr[Exp(GuessO, A).main() @ &m :
                       bad_ev Mem.chal (fdom Mem.m)])).
+ by rewrite Pr [mu_or]; smt(ge0_mu).
rewrite (pr_guess_ideal &m P).
have hbad : Pr[Exp(GuessO, A).main() @ &m : bad_ev Mem.chal (fdom Mem.m)]
            <= (qC * qH)%r / cardMin%r
             + (qC * (qC - 1))%r / (2%r * cardMin%r).
+ rewrite (pr_guess_lro &m) (pr_lro_ro &m) -hsum.
  apply (ler_trans (Pr[G4.main() @ &m : res])); first exact (pr_ro_g4 &m).
  apply (ler_trans (Pr[G3.main() @ &m : Smp.bad /\ size Mem.chal <= qC]));
    first exact (pr_g4_g3 &m).
  exact (pr_g3_fel &m).
smt().
qed.

end section PROOF.
