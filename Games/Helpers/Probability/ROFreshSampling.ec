(* ==================================================================== *)
(* ROFreshSampling: the RO at a hidden fresh point looks uniform          *)
(*                                                                        *)
(* EasyCrypt proof of the ProofFrog statistical helper game pair in the    *)
(* co-located ROFreshSampling.game:                                        *)
(*                                                                        *)
(*   Real.Hash(x)       : return H(x)                                     *)
(*   Real.Challenge()   : val <- D; return H(val)   (val never revealed)  *)
(*   Ideal.Hash(x)      : return H(x)                                     *)
(*   Ideal.Challenge()  : y <- BitString<n>; return y                     *)
(*                                                                        *)
(* The advertised bound is (q_chal^2/2 + q_chal*q_hash) / |D|; we prove   *)
(* the slightly tighter                                                   *)
(*                                                                        *)
(*   adv <= q_chal*q_hash / |D|  +  q_chal*(q_chal-1) / (2*|D|).          *)
(*                                                                        *)
(* Modeling notes.                                                        *)
(*  - The game-owned random function H : D -> R is modeled as a lazily    *)
(*    sampled finite map (modeling default #2's PROM-style choice); the   *)
(*    .game's eagerly sampled Function is observationally equivalent      *)
(*    through oracle access only.  The codomain only needs a lossless     *)
(*    distribution dR (BitString<n> in the .game); uniformity of dR is    *)
(*    NOT required: the proof couples Real's fresh H(val) sample with     *)
(*    Ideal's fresh y sample directly.                                    *)
(*  - Query budgets qH (Hash) and qC (Challenge) are enforced by the      *)
(*    experiment wrapper, as in SamplingWithoutReplacement.ec.            *)
(*                                                                        *)
(* Proof shape.                                                           *)
(*  1. Real is identical to an instrumented Ideal (GuessO: samples val,   *)
(*     answers a fresh y) until BAD = "some challenge point collides      *)
(*     with another challenge point or with a Hash query".                *)
(*  2. The instrumented Ideal equals Ideal (val is dead code).            *)
(*  3. Pr[BAD] cannot be bounded by fel directly: a Hash query hitting    *)
(*     an OLD challenge point involves no sampling at detection time      *)
(*     (the same pre-sampled-secret obstruction as in                     *)
(*     RandomTargetGuessing.ec, with adaptively many targets sampled      *)
(*     inside the oracle).  We therefore present the challenge points as  *)
(*     a PROM random oracle over the challenge INDEX (in_t = int) that    *)
(*     the ideal game reads lazily, apply PROM.FullEager.RO_LRO to        *)
(*     presample them in an up-front loop, swap that (now dead) loop      *)
(*     past the adversary run, and only then latch BAD at sampling time,  *)
(*     where a Birthday-style fel closes with per-step rate (qH+k)/|D|.   *)
(* ==================================================================== *)

require import AllCore List FSet FMap Distr StdOrder StdBigop.
(*---*) import RealOrder Bigreal BRA.
require import Mu_mem FelTactic.
require (*--*) PROM.

(* The finite challenge domain D, with its uniform distribution dD. *)
type D.

clone import MFinite as FinD with type t <- D.

op dD : D distr = FinD.dunifin.
op cardD : int = FinD.Support.card.

lemma dD_ll : is_lossless dD.
proof. exact FinD.dunifin_ll. qed.

lemma dD1E (x : D) : mu1 dD x = 1%r / cardD%r.
proof. exact FinD.dunifin1E. qed.

lemma cardD_gt0 : 0 < cardD.
proof. exact FinD.Support.card_gt0. qed.

lemma mu_dD_mem (X : D fset) : mu dD (mem X) <= (card X)%r / cardD%r.
proof.
have -> : (card X)%r / cardD%r = (card X)%r * (1%r / cardD%r) by smt().
apply (mu_mem_le X dD (1%r / cardD%r)).
move=> x _; rewrite dD1E //.
qed.

(* The hash codomain R: any lossless distribution. *)
type R.

op dR : R distr.

axiom dR_ll : is_lossless dR.

(* query budgets *)
op qH : { int | 0 <= qH } as qH_ge0.
op qC : { int | 0 <= qC } as qC_ge0.

(* The PROM random oracle holding the challenge points, indexed by the
   challenge counter.  Only proof machinery; the games below never expose
   it. *)
clone PROM.FullRO as VI with
  type in_t    <- int,
  type out_t   <- D,
  op   dout    <- (fun (_ : int) => dD),
  type d_in_t  <- unit,
  type d_out_t <- bool.

(* -------------------------------------------------------------------- *)
(* Module interfaces.                                                     *)
(* -------------------------------------------------------------------- *)

module type Oracles = {
  proc hash(x : D) : R
  proc chal() : R
}.

module type Adv (O : Oracles) = {
  proc run() : bool { O.hash, O.chal }
}.

module type RawG = {
  proc init() : unit
  proc fhash(x : D) : R
  proc fchal() : R
}.

(* Shared game state: the lazy RO map and the challenge-point log
   (a ghost in the ideal worlds). *)
module Mem = {
  var m    : (D, R) fmap
  var chal : D list
}.

(* Real world: Challenge evaluates the RO at a hidden fresh point.
   Both procs sample unconditionally and store on a miss (PROM get
   style) so that fresh samples couple one-one with the ideal world. *)
module RealO : RawG = {
  proc init() : unit = {
    Mem.m    <- empty;
    Mem.chal <- [];
  }

  proc fhash(x : D) : R = {
    var y;
    y <$ dR;
    if (x \notin Mem.m) {
      Mem.m.[x] <- y;
    }
    return oget Mem.m.[x];
  }

  proc fchal() : R = {
    var v, y;
    v <$ dD;
    y <$ dR;
    if (v \notin Mem.m) {
      Mem.m.[v] <- y;
    }
    return oget Mem.m.[v];
  }
}.

(* Ideal world: Challenge returns an independent fresh sample
   (matches the .game's Ideal). *)
module IdealO : RawG = {
  proc init = RealO.init

  proc fhash = RealO.fhash

  proc fchal() : R = {
    var y;
    y <$ dR;
    return y;
  }
}.

(* Bridge: ideal answers, but still samples and logs the challenge
   points (dead code for the adversary's view). *)
module GuessO : RawG = {
  proc init = RealO.init

  proc fhash = RealO.fhash

  proc fchal() : R = {
    var v, y;
    v <$ dD;
    Mem.chal <- Mem.chal ++ [v];
    y <$ dR;
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

    proc hash(x : D) : R = {
      var r;
      r <- witness;
      if (cH < qH) {
        r  <@ O.fhash(x);
        cH <- cH + 1;
      }
      return r;
    }

    proc chal() : R = {
      var r;
      r <- witness;
      if (cC < qC) {
        r  <@ O.fchal();
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
abbrev bad_ev (chal : D list) (hashed : D fset) : bool =
  !uniq chal \/ has (mem hashed) chal.

(* -------------------------------------------------------------------- *)
(* The advantage bound.                                                   *)
(* -------------------------------------------------------------------- *)

section PROOF.

declare module A <: Adv {-Mem, -Exp, -VI.RO, -VI.FRO}.

declare axiom A_ll :
  forall (O <: Oracles {-A}),
    islossless O.hash => islossless O.chal => islossless A(O).run.

(* Ideal-world oracles with no challenge-point bookkeeping at all
   (the post-eager games use these). *)
local module O2 : Oracles = {
  proc hash(x : D) : R = {
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

  proc chal() : R = {
    var r, y;
    r <- witness;
    if (Exp.WO.cC < qC) {
      y         <$ dR;
      r         <- y;
      Exp.WO.cC <- Exp.WO.cC + 1;
    }
    return r;
  }
}.

(* The PROM distinguisher: like Exp(GuessO, A), but the challenge points
   come from the index-RO V; the up-front sample loop is a no-op for LRO
   (lazy = GuessO) and a presampling pass for RO (eager). *)
local module DV (V : VI.RO) = {
  module O : Oracles = {
    proc hash(x : D) : R = {
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

    proc chal() : R = {
      var r, v, y;
      r <- witness;
      if (Exp.WO.cC < qC) {
        v         <@ V.get(Exp.WO.cC);
        Mem.chal  <- Mem.chal ++ [v];
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

(* Presampled challenge points as a plain list, loop before the run
   (the adversary's oracles no longer read them). *)
local module G4 = {
  var chalF : D list

  proc main() : bool = {
    var i, r, v;
    Mem.m     <- empty;
    Mem.chal  <- [];
    Exp.WO.cH <- 0;
    Exp.WO.cC <- 0;
    chalF     <- [];
    i <- 0;
    while (i < qC) {
      v     <$ dD;
      chalF <- chalF ++ [v];
      i     <- i + 1;
    }
    r <@ A(O2).run();
    return bad_ev chalF (fdom Mem.m);
  }
}.

(* Challenge points sampled after the run, bad latched at sampling time. *)
local module Smp = {
  var bad : bool

  proc s() : unit = {
    var v;
    v        <$ dD;
    bad      <- bad \/ v \in Mem.chal \/ v \in fdom Mem.m;
    Mem.chal <- Mem.chal ++ [v];
  }
}.

local module G3 = {
  proc main() : unit = {
    var i, r;
    Mem.m     <- empty;
    Mem.chal  <- [];
    Exp.WO.cH <- 0;
    Exp.WO.cC <- 0;
    Smp.bad   <- false;
    r <@ A(O2).run();
    i <- 0;
    while (i < qC) {
      Smp.s();
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
    + (* x in m{1} \ m{2}: x is an old challenge point, so bad fires *)
      have hxchal : x{2} \in Mem.chal{2}.
      + smt(mem_fdom in_fsetU mem_oflist).
      have hcontra : has (mem (fdom Mem.m{2}.[x{2} <- yL])) Mem.chal{2}.
      + by rewrite hasP; exists x{2}; smt(mem_fdom mem_set).
      smt().
  + split=> hx1.
    + (* x in m{2} but not m{1}: contradicts dom inclusion *)
      smt(mem_fdom in_fsetU).
    + by rewrite (hval _ hx2).
+ move=> &2 bad_h; proc; sp; if => //.
  by inline *; auto => />; smt(dR_ll).
+ move=> _; proc; sp; if => //.
  inline *; auto => />; smt(dR_ll cat_uniq has_cat mem_fdom_set hasP hasPn).
+ proc; sp; if => //.
  inline *; auto => /> &1 &2 hnb hval hdom hlt vL hvL yL hyL.
  split=> hv1.
  + (* fresh challenge point: both worlds return the coupled fresh y *)
    move=> hnb'.
    split; first by rewrite get_set_sameE.
    split; first by smt(get_setE mem_cat cats1 rcons_uniq mem_fdom hasP).
    rewrite fdom_set hdom fsetP => z.
    by rewrite !in_fsetU in_fset1 mem_oflist mem_oflist mem_cat /#.
  + (* v already in m{1}: v was hashed or an old challenge, so bad fires *)
    move=> hnb'.
    have : vL \in fdom Mem.m{2} \/ vL \in Mem.chal{2}.
    + smt(mem_fdom in_fsetU mem_oflist).
    case=> [hvm2 | hvch].
    + have : has (mem (fdom Mem.m{2})) (Mem.chal{2} ++ [vL]).
      + by rewrite hasP; exists vL; smt(mem_cat).
      smt().
    + smt(cats1 rcons_uniq).
+ move=> &2 bad_h; proc; sp; if => //.
  by inline *; auto => />; smt(dR_ll dD_ll).
+ move=> _; proc; sp; if => //.
  inline *; auto => />; smt(dD_ll dR_ll cat_uniq has_cat hasP hasPn mem_cat).
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
  inline *; wp; rnd; wp; rnd{1}; auto => />; smt(dD_ll).
by inline *; auto.
qed.

(* ------------------------------------------------------------------ *)
(* Step 3a: present the challenge points as a lazy index-RO.            *)
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
(* the LRO presample loop is a loop of no-ops *)
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
have h := VI.FullEager.RO_LRO DV _; first by move=> _; exact dD_ll.
by rewrite eq_sym; byequiv h.
qed.

(* ------------------------------------------------------------------ *)
(* Step 3c: the eager index-RO is a presampled list; the adversary's    *)
(* oracles no longer read it.                                           *)
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
        Mem.chal{1} = take Exp.WO.cC{2} G4.chalF{2} /\
        (forall j, 0 <= j < qC =>
           VI.RO.m{1}.[j] = Some (nth witness G4.chalF{2} j))).
+ by proc; sp; if => //; inline *; auto.
+ proc; sp; if => //.
  inline *.
  rcondf{1} 3; first by auto => />; smt(domE).
  wp; rnd; wp; rnd{1}; auto => />.
  smt(take_nth cats1 dD_ll).
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
split; first by smt(mem_empty qC_ge0).
move=> mL chF h1 h1' hge hle hnth hfresh.
split; first by smt(take0).
move=> _ hsz _ _ mL1 cCR mR hc0 hcq _ hbad.
case: hbad => [hnu | hhas].
+ left.
  have hcat := cat_take_drop cCR chF.
  smt(cat_uniq).
+ right.
  move: hhas; rewrite !hasP => -[z] [hz1 hz2].
  by exists z; smt(mem_take).
qed.

(* ------------------------------------------------------------------ *)
(* Step 3d: move the (dead) presample loop after the run and latch bad. *)
(* ------------------------------------------------------------------ *)

local lemma pr_g4_g3 &m :
  Pr[G4.main() @ &m : res]
  <= Pr[G3.main() @ &m : Smp.bad /\ size Mem.chal <= qC].
proof.
byequiv (: ={glob A} ==>
           res{1} => (Smp.bad /\ size Mem.chal <= qC){2}) => //.
proc.
swap{1} [6..7] 1.
(* couple the post-run sampling loops *)
while (={i, Mem.m} /\ 0 <= i{1} <= qC /\
       G4.chalF{1} = Mem.chal{2} /\
       size Mem.chal{2} = i{2} /\
       Smp.bad{2} = bad_ev Mem.chal{2} (fdom Mem.m{2})).
+ inline *; auto => />.
  smt(size_cat cat_uniq has_cat hasP).
wp.
call (: ={Mem.m, Exp.WO.cH, Exp.WO.cC}).
+ by proc; sp; if => //; inline *; auto.
+ by proc; sp; if => //; inline *; auto.
auto => />.
smt(fdom0 qC_ge0).
qed.

(* ------------------------------------------------------------------ *)
(* Step 4: the failure-event lemma, Birthday style.                     *)
(* ------------------------------------------------------------------ *)

local lemma pr_g3_fel &m :
  Pr[G3.main() @ &m : Smp.bad /\ size Mem.chal <= qC]
  <= bigi predT (fun k => (qH + k)%r / cardD%r) 0 qC.
proof.
fel 5 (size Mem.chal)
    (fun k => (qH + k)%r / cardD%r)
    qC
    Smp.bad
    [Smp.s : true; O2.hash : false]
    (card (fdom Mem.m) <= Exp.WO.cH /\ Exp.WO.cH <= qH) => //.
+ (* the init prefix establishes the invariant *)
  by auto => />; smt(fdom0 fcards0 qH_ge0).
+ (* O2.hash neutrality: preserves bad and counter, keeps invariant *)
  move=> b c; proc; sp; if => //; inline *; auto => />.
  smt(fdom_set fcardU1 fcard_ge0 size_ge0).
+ (* Smp.s: the per-sample guessing bound *)
  proc; wp; rnd; skip => /> &hr hc0 hcq hnbad hcard hqh.
  apply (ler_trans (mu dD (mem (oflist Mem.chal{hr} `|` fdom Mem.m{hr})))).
  + by apply mu_sub => v; rewrite in_fsetU mem_oflist /#.
  apply (ler_trans ((card (oflist Mem.chal{hr} `|` fdom Mem.m{hr}))%r
                    / cardD%r)).
  + exact mu_dD_mem.
  have hcint : card (oflist Mem.chal{hr} `|` fdom Mem.m{hr})
               <= qH + size Mem.chal{hr}.
  + have h1 := fcardU (oflist Mem.chal{hr}) (fdom Mem.m{hr}).
    have h2 := fcard_oflist Mem.chal{hr}.
    smt(fcard_ge0).
  have hcd := cardD_gt0.
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
     + (qC * qH)%r / cardD%r
     + (qC * (qC - 1))%r / (2%r * cardD%r).
proof.
have hsum : bigi predT (fun k => (qH + k)%r / cardD%r) 0 qC
            = (qC * qH)%r / cardD%r + (qC * (qC - 1))%r / (2%r * cardD%r).
+ have -> : (fun (k : int) => (qH + k)%r / cardD%r)
            = (fun (k : int) => qH%r / cardD%r + k%r * (1%r / cardD%r)).
  + by apply fun_ext => k; smt().
  rewrite big_split sumri_const 1:qC_ge0 -mulr_suml sumidE 1:qC_ge0.
  smt(cardD_gt0).
apply (ler_trans (Pr[Exp(GuessO, A).main() @ &m :
                       P res \/ bad_ev Mem.chal (fdom Mem.m)])).
+ exact (pr_real_guess &m P).
apply (ler_trans (Pr[Exp(GuessO, A).main() @ &m : P res]
                + Pr[Exp(GuessO, A).main() @ &m :
                       bad_ev Mem.chal (fdom Mem.m)])).
+ by rewrite Pr [mu_or]; smt(ge0_mu).
rewrite (pr_guess_ideal &m P).
have hbad : Pr[Exp(GuessO, A).main() @ &m : bad_ev Mem.chal (fdom Mem.m)]
            <= (qC * qH)%r / cardD%r
             + (qC * (qC - 1))%r / (2%r * cardD%r).
+ rewrite (pr_guess_lro &m) (pr_lro_ro &m) -hsum.
  apply (ler_trans (Pr[G4.main() @ &m : res])); first exact (pr_ro_g4 &m).
  apply (ler_trans (Pr[G3.main() @ &m : Smp.bad /\ size Mem.chal <= qC]));
    first exact (pr_g4_g3 &m).
  exact (pr_g3_fel &m).
smt().
qed.

end section PROOF.
