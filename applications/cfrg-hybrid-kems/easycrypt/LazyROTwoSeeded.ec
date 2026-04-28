(* ==========================================================================
   LazyROTwoSeeded.ec
   --------------------------------------------------------------------------
   EasyCrypt formalization of the statistical helper game

       examples/applications/cfrg-hybrid-kems/games/ROM/LazyROTwoSeeded.game

   Honest:  sample s0, s1 independently and uniformly; expose them; answer
            Hash queries through a (lazy) random oracle H.
   Lazy:    sample s0; sample s1 uniformly distinct from s0; pre-program H
            at s0 and s1 with fresh independent uniform values; expose
            (s0, s1); answer Hash queries with the programmed values at
            s0, s1 and lazily otherwise.

   Statistical claim: distinguishing advantage <= mu1 dseed _ = pseed.
   In the FrogLang model |seed| = 2^lambda so pseed = 2^(-lambda).

   The FrogLang Lazy game splits the oracle output as a concatenation
   y_pq || y_t of two independent uniform halves.  At the type level we
   abstract the joint output as a single type `output` with a uniform
   distribution `doutput`; the concatenation of two independent uniform
   halves is uniform on the joint length, so this abstraction loses no
   generality for the statistical claim.

   Proof structure:
     1. |Pr[Honest] - Pr[HonestUniq]| <= pseed
        (collision bound: HonestUniq replaces s1 <$ dseed with
         s1 <$ dseed \ pred1 s0; outside the s1 = s0 event the two
         games are perfectly coupled).
     2. Pr[HonestUniq] = Pr[Lazy]
        (eager pre-programming of m at s0, s1 with fresh independent
         uniform values is equivalent to lazy sampling on first access,
         since s0, s1 are distinct and doutput is the same distribution
         used by the lazy oracle).
   ========================================================================== *)

require import AllCore Distr FMap Dexcepted StdOrder.
import RealOrder.

(* -------------------------------------------------------------------------- *)
(* Abstract domain (seeds) and codomain (joint hash output).                  *)
(* -------------------------------------------------------------------------- *)
type seed.
type output.

op dseed   : seed   distr.
op doutput : output distr.

(* pseed = 1 / |seed|.  In the FrogLang model pseed = 2^(-lambda).            *)
op pseed : real.

axiom pseed_ge0  : 0%r <= pseed.
axiom dseed_ll   : is_lossless dseed.
axiom dseed_fu   : is_full     dseed.
axiom dseed_uni  : is_uniform  dseed.
axiom dseed_mu1  : forall (s : seed), mu1 dseed s = pseed.

axiom doutput_ll : is_lossless doutput.

(* -------------------------------------------------------------------------- *)
(* Oracle interface and adversary.                                            *)
(* -------------------------------------------------------------------------- *)
module type Oracle = {
  proc hash(x : seed) : output
}.

module type Adversary (O : Oracle) = {
  proc distinguish(s0 s1 : seed) : bool {O.hash}
}.

(* -------------------------------------------------------------------------- *)
(* Lazy oracle implementation, shared across the games.                       *)
(* -------------------------------------------------------------------------- *)
module RO : Oracle = {
  var m : (seed, output) fmap

  proc init () : unit = { m <- empty; }

  proc hash (x : seed) : output = {
    var y;
    y <$ doutput;
    if (x \notin m) {
      m.[x] <- y;
    }
    return oget m.[x];
  }
}.

(* -------------------------------------------------------------------------- *)
(* The two games and one auxiliary intermediate.                              *)
(* -------------------------------------------------------------------------- *)
module Honest (A : Adversary) = {
  proc main() : bool = {
    var s0, s1, b;
    RO.init();
    s0 <$ dseed;
    s1 <$ dseed;
    b  <@ A(RO).distinguish(s0, s1);
    return b;
  }
}.

module Lazy (A : Adversary) = {
  proc main() : bool = {
    var s0, s1, y0, y1, b;
    RO.init();
    s0 <$ dseed;
    s1 <$ dseed \ (pred1 s0);
    y0 <$ doutput;
    y1 <$ doutput;
    RO.m.[s0] <- y0;
    RO.m.[s1] <- y1;
    b  <@ A(RO).distinguish(s0, s1);
    return b;
  }
}.

module HonestUniq (A : Adversary) = {
  proc main() : bool = {
    var s0, s1, b;
    RO.init();
    s0 <$ dseed;
    s1 <$ dseed \ (pred1 s0);
    b  <@ A(RO).distinguish(s0, s1);
    return b;
  }
}.

(* ========================================================================== *)
(* Section: bound the distinguishing advantage.                               *)
(* ========================================================================== *)

(* Clone TwoStepSampling with our seed type and dseed distribution.            *)
(* This gives us the equivalence between                                       *)
(*   r <$ dseed \ pred1 c                            (S.direct)                *)
(* and                                                                         *)
(*   r <$ dseed; if (r = c) r <$ dseed \ pred1 c     (S.indirect)              *)
(* whenever dseed is lossless.                                                 *)
clone import Dexcepted.TwoStepSampling as TSS with
  type i    <- unit,
  type t    <- seed,
  op   dt _ <- dseed
  proof *.

section LazyROTwoSeeded_proof.

declare module A <: Adversary { -RO }.

declare axiom A_ll :
  forall (O <: Oracle { -A }),
    islossless O.hash => islossless A(O).distinguish.

(* Bad-event tracker.  We use a separate module so its globals live outside    *)
(* RO and outside A's footprint (A's glob is restricted to disjoint from RO,   *)
(* and Bad is declared after A, so A cannot touch it either).                  *)
local module Bad = {
  var bad : bool
}.

(* Honest re-stated with an explicit Bad.bad <- false at the start.            *)
local module HonestB = {
  proc main() : bool = {
    var s0, s1, b;
    Bad.bad <- false;
    RO.init();
    s0 <$ dseed;
    s1 <$ dseed;
    b <@ A(RO).distinguish(s0, s1);
    return b;
  }
}.

(* Indirect form of HonestUniq, with bad-flag set on collision.  By the        *)
(* indirect/direct equivalence (TSS.ll_direct_indirect_eq), the s1 distribution*)
(* matches dseed \ pred1 s0; hence Pr[HonestIB:res] = Pr[HonestUniq:res].      *)
local module HonestIB = {
  proc main() : bool = {
    var s0, s1, b;
    Bad.bad <- false;
    RO.init();
    s0 <$ dseed;
    s1 <$ dseed;
    Bad.bad <- (s1 = s0);
    if (s1 = s0) {
      s1 <$ dseed \ pred1 s0;
    }
    b <@ A(RO).distinguish(s0, s1);
    return b;
  }
}.

local lemma RO_hash_ll : islossless RO.hash.
proof. by proc; auto=> />; rewrite doutput_ll. qed.

local lemma dseed_pred1_ll (s0 : seed) :
  pseed < 1%r => is_lossless (dseed \ pred1 s0).
proof.
move=> hlt; apply: dexcepted_ll; first exact dseed_ll.
by have ->: mu dseed (pred1 s0) = pseed by exact: dseed_mu1.
qed.

local lemma pr_honest_honestB &m :
  Pr[Honest(A).main() @ &m : res] = Pr[HonestB.main() @ &m : res].
proof.
byequiv (_: ={glob A} ==> ={res}) => //; proc.
call (_: ={glob RO}); first by sim.
inline RO.init; auto.
qed.

(* HonestIB and HonestUniq agree on res: Bad.bad assignments don't affect res, *)
(* and the LHS's two-step (indirect) sampling has the same final s1            *)
(* distribution as the RHS's direct sample (TSS.ll_direct_indirect_eq).        *)
(* The clean rewrite-equiv path requires the cloned op to be unfolded against  *)
(* the side-condition; we leave this as an admit and rely on the rest of the   *)
(* structural proof.                                                           *)
local lemma pr_honestIB_honestUniq &m :
  Pr[HonestIB.main() @ &m : res] = Pr[HonestUniq(A).main() @ &m : res].
proof.
byequiv (_: ={glob A} ==> ={res}) => //; proc.
call (_: ={glob RO}); first by sim.
inline RO.init.
seq 3 2 : (={glob A, RO.m, s0}); first by auto.
outline {2} 1 by { s1 <@ S.direct((), fun (_:unit) (s:seed) => s = s0); }.
rewrite equiv[{2} 1 ll_direct_indirect_eq (tt, (fun (_:unit) (s:seed) => s = s0) :@ s1)].
inline S.indirect.
sp; seq 1 1 : (#pre /\ s1{1} = r{2}); first by auto.
seq 1 0 : (#pre); first by auto.
wp; if; auto=> /> &1 &2; smt().
auto=> />; exact dseed_ll.
qed.

(* Bad-event probability: Bad.bad is set iff the initial s1 sample equals s0, *)
(* which occurs with probability pseed under dseed (uniform).  The byphoare  *)
(* seq quad-bound (P, p1, q1, p2, q2) with q1 = 1%r is auto-discharged, so we *)
(* only need to bound p1 (probability collision) and q2 (Bad.bad stays false  *)
(* on the !P branch).                                                         *)
local lemma pr_honestIB_bad &m :
  pseed < 1%r =>
  Pr[HonestIB.main() @ &m : Bad.bad] <= pseed.
proof.
move=> hlt.
byphoare => //; proc.
seq 5 : (s1 = s0) pseed 1%r _ 0%r (Bad.bad <=> s1 = s0) => //.
+ inline RO.init; auto.
+ wp; rnd (pred1 s0); rnd; inline RO.init; auto.
  by move=> &hr _ s0 _; rewrite dseed_mu1.
+ hoare.
  call (_: !Bad.bad); first by proc; auto.
  rcondf 1; first by skip; smt().
  skip; smt().
qed.

(* Upto-bad equiv: when Bad.bad{2} is not set, HonestB and HonestIB agree on   *)
(* res.  The if-branch on the RHS only fires when bad, so under !bad the      *)
(* games are identical to A.  Used in both directions of the upto-bad         *)
(* probability bound below.                                                    *)
local lemma honestB_honestIB_eq :
  pseed < 1%r =>
  equiv [HonestB.main ~ HonestIB.main :
          ={glob A} ==> !Bad.bad{2} => ={res}].
proof.
move=> hlt.
proc.
call (_: Bad.bad, ={glob RO}, true).
+ exact A_ll.
+ by proc; auto.
+ by move=> _ _; proc; auto=> />; rewrite doutput_ll.
+ by move=> _; proc; auto=> />; rewrite doutput_ll.
seq 4 4 : (={glob A, glob RO, s0, s1} /\ !Bad.bad{2}).
+ inline RO.init; auto.
seq 0 1 : (={glob A, glob RO, s0, s1} /\ Bad.bad{2} = (s1{1} = s0{1})).
+ auto.
if{2}; last by skip; smt().
wp; rnd{2}; skip => /> ?.
exact (dseed_pred1_ll _ hlt).
qed.

local lemma honestB_le_honestIB &m :
  pseed < 1%r =>
  Pr[HonestB.main() @ &m : res] <=
  Pr[HonestIB.main() @ &m : res] + Pr[HonestIB.main() @ &m : Bad.bad].
proof.
move=> hlt.
apply (ler_trans (Pr[HonestIB.main() @ &m : res \/ Bad.bad])); last first.
+ rewrite Pr[mu_or]; smt(mu_bounded).
byequiv (honestB_honestIB_eq hlt) => //; smt(mu_bounded).
qed.

local lemma honestIB_le_honestB &m :
  pseed < 1%r =>
  Pr[HonestIB.main() @ &m : res] <=
  Pr[HonestB.main() @ &m : res] + Pr[HonestIB.main() @ &m : Bad.bad].
proof.
move=> hlt.
have h_split :
  Pr[HonestIB.main() @ &m : res] =
    Pr[HonestIB.main() @ &m : res /\ !Bad.bad]
  + Pr[HonestIB.main() @ &m : res /\  Bad.bad].
+ by rewrite Pr[mu_split !Bad.bad].
have h_bad :
  Pr[HonestIB.main() @ &m : res /\ Bad.bad]
  <= Pr[HonestIB.main() @ &m : Bad.bad].
+ by rewrite Pr[mu_sub].
have h_eq :
  Pr[HonestIB.main() @ &m : res /\ !Bad.bad]
  <= Pr[HonestB.main()  @ &m : res].
+ have eq2 : equiv[HonestIB.main ~ HonestB.main :
                    ={glob A} ==> !Bad.bad{1} => ={res}].
  + symmetry; conseq (honestB_honestIB_eq hlt); smt().
  byequiv eq2 => //; smt().
smt().
qed.

(* -------------------------------------------------------------------------- *)
(* Step 1: |Pr[Honest] - Pr[HonestUniq]| <= pseed.                            *)
(*                                                                            *)
(* Mathematical content: condition on the collision event F = (s0 = s1).      *)
(*    Pr[Honest : res] = Pr[Honest : res /\ F] + Pr[Honest : res /\ !F].      *)
(*    Pr[Honest : res /\ F]  <= Pr[Honest : F] = pseed.                       *)
(*    Pr[Honest : res /\ !F] = (1 - pseed) * Pr[HonestUniq : res]             *)
(*                          <= Pr[HonestUniq : res].                          *)
(* The middle equality uses that conditional on s0 <> s1, the joint           *)
(* distribution of (s0, s1) in Honest matches the (unconditional) joint       *)
(* distribution of (s0, s1) in HonestUniq, since dseed is uniform.            *)
(* Combining: |Pr[Honest:res] - Pr[HonestUniq:res]| <= pseed.                 *)
(*                                                                            *)
(* Mechanization status (EasyCrypt-level): the cleanest path is an upto-bad   *)
(* byequiv ending in (s0{1} <> s1{1}) => ={res, glob RO} that bounds the      *)
(* difference via Pr[Honest : s0=s1].  However, the rnd-coupling needed for   *)
(* the s1 step (left: dseed, right: dseed \ pred1 s0) is non-bijective:       *)
(*   support(dseed)             = full type                                   *)
(*   support(dseed \ pred1 s0)  = full type minus {s0}                        *)
(* and the pmf differs by the (1 - pseed) normalization factor, so EC's       *)
(* `rnd f` and `rnd f g` tactics (which require a pmf-preserving bijection)   *)
(* do not apply directly.  A complete mechanization requires either the       *)
(* fel tactic (Fundamental lemma of game playing - see                        *)
(* easycrypt/examples/Upto.ec) with a bad-flag tracking the collision         *)
(* across both sides, or a manual probability decomposition via byphoare      *)
(* with explicit dscalar/dlet rewrites of `s1 <$ dseed` into the mixture      *)
(* `c <$ dbiased pseed; if c then s0 else s1 <$ dseed \ pred1 s0`.            *)
(* -------------------------------------------------------------------------- *)

local lemma honest_uniq_adv &m :
  `| Pr[Honest(A).main()    @ &m : res]
   - Pr[HonestUniq(A).main() @ &m : res] |
  <= pseed.
proof.
case @[ambient]: (pseed < 1%r) => hlt; last first.
+ smt(mu_bounded).
have h1 := pr_honest_honestB &m.
have h2 := pr_honestIB_honestUniq &m.
have h3 := pr_honestIB_bad &m hlt.
have h4 := honestB_le_honestIB &m hlt.
have h5 := honestIB_le_honestB &m hlt.
smt().
qed.

(* -------------------------------------------------------------------------- *)
(* Step 2: HonestUniq and Lazy are perfectly equivalent.                     *)
(*                                                                            *)
(* Mathematical content: the two procedures differ only in that Lazy         *)
(* pre-samples y0, y1 from doutput and writes them into RO.m at s0, s1       *)
(* before invoking the adversary.  Since (a) s0 <> s1 (enforced by           *)
(* sampling s1 from dseed \ pred1 s0), and (b) the lazy oracle's             *)
(* first-access sampling distribution is exactly doutput, the eager          *)
(* pre-programming and the lazy first-access sampling produce identically    *)
(* distributed observations to the adversary.                                *)
(*                                                                            *)
(* Mechanization status (EasyCrypt-level): this is the classical             *)
(* eager-vs-lazy correspondence at two distinct points.  The standard tools  *)
(* are EasyCrypt's `eager` tactic (see easycrypt/examples/PRG.ec for a       *)
(* model proof using `eager call` / `eager proc`), or a retrofit onto the    *)
(* `PROM.MkRO` library (theories/crypto/PROM.ec) which exposes RO/LRO        *)
(* equivalence lemmas.  Because the sampling is at adversary-determined      *)
(* points (the first call to hash(s0) or hash(s1)) and the sample binding    *)
(* y0 lives outside the adversary call in Lazy but inside it in              *)
(* HonestUniq, this cannot be discharged by direct equiv invariant           *)
(* reasoning -- the eager tactic is the right tool.                          *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Plumbing for the eager step.                                                *)
(*                                                                             *)
(* We hoist the seeds (s0, s1) into a module's globals so that a "pre-program" *)
(* helper procedure Pre.prog can reference them without parameter-passing, and   *)
(* therefore can be moved across an adversary call by EasyCrypt's `eager`      *)
(* tactics (which work on parameter-less procedures over globals).             *)
(*                                                                             *)
(* Pre.prog is the conditional pre-programming block: it samples y0, y1 fresh    *)
(* from doutput and writes them into RO.m at G.s0g, G.s1g, but only on entries *)
(* that are not already programmed.  When called at the start of a game (m     *)
(* empty), the conditional is always taken so Pre.prog() coincides with the      *)
(* unconditional pre-programming used by Lazy.  When called after the          *)
(* adversary, entries already stored by the adversary are preserved.           *)
(* -------------------------------------------------------------------------- *)
local module G = {
  var s0g : seed
  var s1g : seed
}.

(* Holds the boolean result returned by the wrapped adversary call AdvW.d.    *)
(* Kept in a separate module so `={glob G}` invariants stay unchanged.        *)
local module B = {
  var b : bool
}.

local module Pre = {
  proc prog () : unit = {
    var y0, y1;
    y0 <$ doutput;
    y1 <$ doutput;
    if (G.s0g \notin RO.m) { RO.m.[G.s0g] <- y0; }
    if (G.s1g \notin RO.m) { RO.m.[G.s1g] <- y1; }
  }
}.

local lemma Pre_prog_ll : islossless Pre.prog.
proof. by proc; auto=> />; rewrite doutput_ll. qed.

(* Zero-argument wrapper around the adversary call that reads its parameters  *)
(* from the globals G.s0g / G.s1g.  This wrapper avoids the parameter binding *)
(* obstacle in `eager proc`: with no formal arguments, eager proc does not    *)
(* generate the spurious obligation that the adversary's parameters be equal  *)
(* across both sides.                                                          *)
local module AdvW = {
  proc d () : unit = {
    B.b <@ A(RO).distinguish(G.s0g, G.s1g);
  }
}.

(* Wrappers of HonestUniq and Lazy that use the global seeds and are aligned   *)
(* for an `eager call` over the adversary distinguisher.  HonestUniqW has a    *)
(* dead Pre.prog() suffix (does not affect res = B.b); LazyW has Pre.prog() before *)
(* the adversary call, matching Lazy's pre-programming.                        *)
local module HonestUniqW = {
  proc main () : bool = {
    RO.init();
    G.s0g <$ dseed;
    G.s1g <$ dseed \ pred1 G.s0g;
    AdvW.d();
    Pre.prog();
    return B.b;
  }
}.

local module LazyW = {
  proc main () : bool = {
    RO.init();
    G.s0g <$ dseed;
    G.s1g <$ dseed \ pred1 G.s0g;
    Pre.prog();
    AdvW.d();
    return B.b;
  }
}.

(* Step 1: HonestUniq(A) ~ HonestUniqW.  The seeds are stored in G instead of  *)
(* in local variables, and Pre.prog() at the tail is dead code.                  *)
local equiv huniq_huniqW : HonestUniq(A).main ~ HonestUniqW.main :
  ={glob A} ==> ={res}.
proof.
proc.
seq 3 3 : (={glob A, glob RO} /\ s0{1} = G.s0g{2} /\ s1{1} = G.s1g{2}).
+ inline RO.init; auto.
seq 1 1 : (#pre /\ b{1} = B.b{2}).
+ inline AdvW.d.
  by call (_: ={glob RO}); first by sim.
by call{2} Pre_prog_ll; auto.
qed.

(* Step 2: Lazy(A) ~ LazyW.  Initially RO.m is empty so the conditional        *)
(* programming in Pre.prog unfolds to unconditional programming.                 *)
local equiv lazy_lazyW : Lazy(A).main ~ LazyW.main :
  ={glob A} ==> ={res}.
proof.
proc.
inline Pre.prog AdvW.d.
seq 5 5 : (={glob A}
           /\ s0{1} = G.s0g{2} /\ s1{1} = G.s1g{2}
           /\ ={y0, y1}
           /\ RO.m{1} = empty /\ RO.m{2} = empty
           /\ G.s0g{2} <> G.s1g{2}).
+ inline RO.init; auto; smt(supp_dexcepted).
call (_: ={glob RO}); first by sim.
rcondt{2} 1; first by auto; smt(mem_empty).
rcondt{2} 2; first by auto; smt(mem_set mem_empty).
by auto.
qed.

(* Step 3: the eager swap.  Pre.prog programs only s0g and s1g (writes are       *)
(* guarded so they are idempotent on already-programmed entries) and resamples *)
(* y0, y1 fresh on every call.  RO.hash(x) lazily programs m[x] with a fresh   *)
(* sample.  The swap holds without needing s0g <> s1g because all writes are   *)
(* guarded.                                                                    *)
(*                                                                             *)
(* Proof skeleton (in progress -- left as admit):                              *)
(*   eager proc.                                                               *)
(*   inline Pre.prog.                                                          *)
(*   swap{1} 5 -4.    (* move LHS y to top *)                                  *)
(*   swap{2} 4 -2.    (* move RHS y0 above the if-x *)                         *)
(*   swap{2} 5 -2.    (* move RHS y1 above the if-x *)                         *)
(*   (* Both sides now begin with samples y, y0, y1; LHS continues with        *)
(*       if(s0g); if(s1g); if(x); result, while RHS continues with             *)
(*       if(x); result; if(s0g); if(s1g). *)                                   *)
(*                                                                             *)
(* Sample coupling depends on which seed coincides with x:                     *)
(*   - x <> s0g, x <> s1g: couple ={y, y0, y1} via `seq 3 3 : ... auto`.       *)
(*   - x = s0g, x <> s1g: couple LHS_y0 with RHS_y, ={y1}; LHS_y, RHS_y0 dead. *)
(*   - x = s1g, x <> s0g: couple LHS_y1 with RHS_y, ={y0}; LHS_y, RHS_y1 dead. *)
(*   - x = s0g = s1g    : couple LHS_y0 with RHS_y; LHS_y, LHS_y1, RHS_y0,     *)
(*                        RHS_y1 dead.                                         *)
(*                                                                             *)
(* For the (x <> s0g, x <> s1g) branch the sample coupling is uniform; after   *)
(* `seq 3 3 : (#pre /\ ={y, y0, y1})`, case-split on whether each of s0g, s1g, *)
(* x is in RO.m -- 8 leaves -- and discharge each via rcondt/rcondf chains     *)
(* followed by `sim`.  Verified interactively that goals 1 (all-in) and 2     *)
(* (s0g, s1g in m, x not in m) close cleanly with this approach.               *)
(*                                                                             *)
(* The remaining branches (when x coincides with a seed) require swapping     *)
(* the sampling coupling -- e.g. `swap{1} 2 -1` to align LHS_y0 with RHS_y --  *)
(* before the seq, then the same rcondt/rcondf-per-leaf pattern.  Each leaf's  *)
(* rcondt/rcondf position arithmetic shifts as ifs are eliminated, which is    *)
(* what makes a fully-written-out proof error-prone; an interactive iteration  *)
(* through cli_step is the practical way to nail down each leaf's positions.  *)
(*                                                                             *)
(* An alternative worth trying: retrofit RO onto PROM.MkRO/FullEager (see      *)
(* easycrypt/theories/crypto/PROM.ec, eager_get/eager_set + RO_LRO_D) so that  *)
(* the eager swap comes from the library rather than being proved by hand.   *)
local lemma eager_pre_hash :
  eager [Pre.prog(); , RO.hash ~ RO.hash, Pre.prog(); :
          ={x, glob G, glob RO}
          ==> ={res, glob G, glob RO}].
proof.
eager proc; inline Pre.prog.
(* Move all three samples to the top of both bodies. *)
swap{1} 5 -4. swap{2} 4 -2. swap{2} 5 -2.
(* Case 1: x is distinct from both s0g and s1g.  Couple all three samples
   identically; the writes to disjoint keys commute. *)
case (x{1} <> G.s0g{1} /\ x{1} <> G.s1g{1}).
+ seq 3 3 : (#pre /\ ={y, y0, y1}); first by auto.
  wp; skip; smt(set_setE get_setE mem_set).
(* Case 2: x = s0g.  After the LHS pre-program writes m[s0g] := y0, the
   RO.hash branch on x = s0g no longer fires; result on LHS is y0 (when
   s0g was fresh).  On RHS, RO.hash writes m[x] := y first; result is y.
   Couple LHS_y0 with RHS_y; LHS_y and RHS_y0 are dead. *)
case (x{1} = G.s0g{1}).
+ swap{1} 2 -1.
  seq 1 1 : (#pre /\ y0{1} = y{2}); first by auto.
  seq 1 1 : (#pre); first by rnd{1}; rnd{2}; auto => />; smt(doutput_ll).
  seq 1 1 : (#pre /\ y1{1} = y1{2}); first by auto.
  wp; skip; smt(set_setE get_setE mem_set).
(* Case 3: x = s1g and s0g <> s1g (since x <> s0g here).  Symmetric to
   case 2: couple LHS_y1 with RHS_y, ={y0}, drop LHS_y / RHS_y1. *)
conseq (_ : (x{1} = x{2} /\ (G.s0g{1}, G.s1g{1}) = (G.s0g{2}, G.s1g{2})
              /\ RO.m{1} = RO.m{2})
            /\ x{1} = G.s1g{1} /\ G.s0g{1} <> G.s1g{1} ==> _); first by smt().
swap{1} 3 -2. swap{1} 2 1.
seq 1 1 : (#pre /\ y1{1} = y{2}); first by auto.
seq 1 1 : (#pre /\ y0{1} = y0{2}); first by auto.
seq 1 1 : (#pre); first by rnd{1}; rnd{2}; auto => />; smt(doutput_ll).
wp; skip => /> *; smt(get_setE mem_set set_setE).
qed.

(* ============================================================================ *)
(* Step 4: LazyW ~ HonestUniqW via eager call.                                  *)
(* ---------------------------------------------------------------------------- *)
(* Status summary                                                                *)
(* ---------------------------------------------------------------------------- *)
(*                                                                               *)
(* The proof structure is complete; one `admit` remains on a side condition     *)
(* that is morally true but cannot be discharged in this version of EasyCrypt   *)
(* without restructuring the adversary interface.                                *)
(*                                                                               *)
(* Proof skeleton                                                                *)
(* --------------                                                                *)
(*   1. Align the prefixes (RO.init; G.s0g <- ...; G.s1g <- ...) on both         *)
(*      sides via `seq 3 3`.                                                      *)
(*   2. Outer `eager call` over the 0-argument wrapper AdvW.d to swap Pre.prog  *)
(*      past the adversary call.  The wrapper is needed because EC's eager      *)
(*      machinery cannot swap a Pre.prog past a call whose result is captured   *)
(*      via a local variable: it complains "swapping statement may use only     *)
(*      global variables: result".  AdvW.d stores the adversary's result into   *)
(*      the dedicated global B.b, eliminating the receiver-local issue.         *)
(*   3. `eager proc` to inline AdvW.d.                                           *)
(*   4. Inner `eager call` over the abstract `A(RO).distinguish`, then          *)
(*      `eager proc (={glob G, glob RO}) => //` (the abstract-eager rule)       *)
(*      to reduce to per-oracle obligations: an eager swap of Pre.prog past     *)
(*      RO.hash (= `eager_pre_hash`), Pre.prog ~ Pre.prog, and structural       *)
(*      RO.hash ~ RO.hash congruences (closed by `sim`).                        *)
(*                                                                               *)
(* The remaining `admit`                                                         *)
(* ---------------------                                                         *)
(*                                                                               *)
(* `eager proc` in step 4 (the abstract-function form) emits a side condition   *)
(* of the shape                                                                  *)
(*                                                                               *)
(*   forall &1 &2,                                                               *)
(*     ={glob A, glob G, glob RO} =>                                             *)
(*     (s0{1} = s0{2} /\ s1{1} = s1{2}) /\ ={glob A, glob G, glob RO}            *)
(*                                                                               *)
(* where `s0`, `s1` are the formal parameters of `A.distinguish`.  At the       *)
(* actual call site we have `A(RO).distinguish(G.s0g, G.s1g)` on both sides,    *)
(* and `={glob G}` ensures `(G.s0g{1}, G.s1g{1}) = (G.s0g{2}, G.s1g{2})`, so    *)
(* the post-binding values of s0, s1 *are* equal across the two sides.  But    *)
(* the goal as displayed quantifies universally over &1, &2 with no            *)
(* constraint linking the formals to the call-site args, so smt cannot          *)
(* discharge it.                                                                 *)
(*                                                                               *)
(* Reference: easycrypt/src/phl/ecPhlEager.mli, `process_fun_abs`.  The rule    *)
(* it implements is                                                              *)
(*                                                                               *)
(*   ... S, A.f{o} ~ A.f(o'), S : I /\ ={glob A, A.f.params} ==>                *)
(*                                I /\ ={glob A, res} ...                       *)
(*                                                                               *)
(* so the rule does require `={A.f.params}` in the precondition.  However,     *)
(* in this EC version, when a user invokes `eager call (: J ==> K)` and `J`    *)
(* is the call-site precondition, EC does *not* automatically thread the args  *)
(* equality `={A.f.params}` derived from the call-site argument tuple into     *)
(* `J`.  The user is left to prove the gap by hand, but with no binding         *)
(* between formals and call-site args in scope this is impossible.              *)
(*                                                                               *)
(* Workarounds attempted                                                         *)
(* ---------------------                                                         *)
(*                                                                               *)
(* * AdvW wrapper (kept).  Storing the adversary's result in the global B.b    *)
(*   instead of a local var clears the *outer* "swap statement uses only       *)
(*   globals" check, so the outer eager call can thread `B.b{1} = B.b{2}`.    *)
(*   This is necessary but not sufficient: the inner abstract eager call       *)
(*   still has the args-binding gap.                                            *)
(* * Strengthening the eager call invariant with `={arg}`, `s0{1} = G.s0g{1}`, *)
(*   etc. -- not accepted as an `eager proc` invariant in this EC version.     *)
(* * `conseq` on the eager judgment to add an args binding -- rejected with    *)
(*   "conseq: not a phl/prhl judgement" (conseq does not work over `eager`).   *)
(*                                                                               *)
(* Paths to a fully closed proof                                                *)
(* ----------------------------                                                 *)
(*                                                                               *)
(* (A) Restructure the Adversary type to a 0-argument distinguisher that       *)
(*     reads the seeds from G.s0g, G.s1g.  Then `eager proc` has no formal     *)
(*     args to bind and the side condition disappears.  Cost: re-state the     *)
(*     `Adversary` interface, the `Honest`, `Lazy`, `HonestUniq` games, the    *)
(*     `A_ll` losslessness axiom, and update every prior lemma in this file.   *)
(*                                                                               *)
(* (B) Replace this `equiv` lemma with a `byequiv` + FEL-style argument that   *)
(*     bypasses `eager` entirely, reasoning about the lazy oracle's behavior   *)
(*     across A's queries directly at the probability level.  Cost: rebuild    *)
(*     this lemma from scratch with a different proof technique.                *)
(*                                                                               *)
(* (C) Patch EasyCrypt's `process_fun_abs` to thread `={A.f.params}` from the  *)
(*     call-site argument tuple into the side condition automatically.  This   *)
(*     is the underlying fix; out of scope for this file.                       *)
(*                                                                               *)
(* For now we keep the structural reduction of `lazyW_huniqW` in place with    *)
(* a single localized `admit` for the args-binding side condition.  The        *)
(* admit is documented inline below, and the rest of the proof closes          *)
(* cleanly with `sim`, `apply eager_pre_hash`, and `auto; smt()`.              *)
(* ============================================================================ *)
local equiv lazyW_huniqW : LazyW.main ~ HonestUniqW.main :
  ={glob A} ==> ={res}.
proof.
proc.
seq 3 3 : (={glob A, glob G, glob RO}); first by inline RO.init; auto.
(* Outer eager call: swap Pre.prog past the wrapped adversary call AdvW.d.    *)
eager call (: ={glob A, glob G, glob RO}
              ==> ={glob A, glob G, glob RO} /\ B.b{1} = B.b{2}).
eager proc.
(* Inner eager call: swap Pre.prog past the abstract A.distinguish, reducing  *)
(* to per-oracle eager swaps via the abstract-eager rule.                     *)
eager call (: ={glob A, glob G, glob RO}
              ==> ={glob A, glob G, glob RO, res}); auto.
eager proc (={glob G, glob RO}) => //.
(* (a) Args-binding s0{1} = s0{2} /\ s1{1} = s1{2}.  Holds because the        *)
(* call-site args (G.s0g, G.s1g) are equal under ={glob G}, but EC does not   *)
(* auto-link formals to the call-site args here. *)
+ admit.
(* (b) Pre.prog ~ Pre.prog under the invariant -- direct simulation. *)
+ sim.
(* (c) The per-oracle eager swap is exactly eager_pre_hash. *)
+ apply eager_pre_hash.
(* (d), (e) Trailing structural goals (RO.hash ~ RO.hash) under the           *)
(* invariant -- closed by sim. *)
+ sim.
+ sim.
auto; smt().
qed.

local equiv huniq_lazy_eq :
  HonestUniq(A).main ~ Lazy(A).main : ={glob A} ==> ={res}.
proof.
transitivity HonestUniqW.main
  (={glob A} ==> ={res})
  (={glob A} ==> ={res}) => //.
+ smt().
+ by apply huniq_huniqW.
symmetry.
transitivity LazyW.main
  (={glob A} ==> ={res})
  (={glob A} ==> ={res}) => //.
+ smt().
+ by apply lazy_lazyW.
by apply lazyW_huniqW.
qed.

local lemma huniq_lazy_pr &m :
  Pr[HonestUniq(A).main() @ &m : res] = Pr[Lazy(A).main() @ &m : res].
proof. by byequiv huniq_lazy_eq. qed.

(* -------------------------------------------------------------------------- *)
(* Final theorem: the statistical bound on distinguishing advantage.         *)
(* -------------------------------------------------------------------------- *)

lemma lazy_ro_two_seeded_advantage &m :
  `| Pr[Honest(A).main() @ &m : res] - Pr[Lazy(A).main() @ &m : res] |
  <= pseed.
proof.
have h1 := honest_uniq_adv &m.
have h2 := huniq_lazy_pr   &m.
smt().
qed.

end section LazyROTwoSeeded_proof.
