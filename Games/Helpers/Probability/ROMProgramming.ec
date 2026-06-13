(* ==================================================================== *)
(* ROMProgramming: programming a random oracle at a known point          *)
(*                                                                        *)
(* EasyCrypt proof of the ProofFrog statistical helper game pair in the    *)
(* co-located ROMProgramming.game:                                         *)
(*                                                                        *)
(*   Natural.Initialize(target)    : H <- Function; return H(target)      *)
(*   Natural.Query(x)              : return H(x)                          *)
(*   Programmed.Initialize(target) : H <- Function; t = target;           *)
(*                                   u <- R; return u                     *)
(*   Programmed.Query(x)           : if x == t return u else return H(x)  *)
(*                                                                        *)
(* The bound is 0: the two games are PERFECTLY indistinguishable for any  *)
(* caller-supplied target and any predicate P on the experiment output.   *)
(* Programming the oracle's value at the (known) target with a fresh      *)
(* uniform u is distributed exactly like its natural lazily-sampled value *)
(* at that point -- the classic one-point reprogramming fact.             *)
(*                                                                        *)
(* Modeling notes.                                                        *)
(*  - The game-owned random function H : D -> R is modeled as a lazily    *)
(*    sampled finite map (modeling default #2), reachable only through    *)
(*    Query; the .game's eagerly sampled Function is observationally      *)
(*    equivalent through oracle access only.  The codomain needs only an  *)
(*    arbitrary distribution dR; neither uniformity nor losslessness is   *)
(*    required (every fresh sample is coupled one-one across the worlds).  *)
(*  - The target is caller-chosen and known to the caller: the adversary  *)
(*    picks it in choose() and then distinguishes with Query access.  No  *)
(*    query budget is needed since the bound is 0 regardless of q.        *)
(*  - NaturalO carries a ghost field tgt recording the init target; it is *)
(*    used only by the proof invariant (never read in Query), so NaturalO *)
(*    is a faithful "return H(x)" oracle.                                 *)
(*                                                                        *)
(* Proof shape.  A single byequiv with the reprogramming invariant        *)
(*   NaturalO.m = ProgrammedO.m  everywhere except at the target, where   *)
(*   NaturalO.m holds exactly ProgrammedO.u (and ProgrammedO.m omits it). *)
(* Query at the target reads u on both sides with no sampling; Query      *)
(* elsewhere reads/lazily-samples a coupled point.  Initialize couples    *)
(* NaturalO's fresh H(target) sample with ProgrammedO's fresh u.          *)
(* ==================================================================== *)

require import AllCore FMap Distr.

(* The oracle domain and codomain.  dR is an arbitrary output            *)
(* distribution (a uniform dR models a true random function; the         *)
(* equivalence holds for any dR). *)
type D.
type R.

op dR : R distr.

(* -------------------------------------------------------------------- *)
(* Module interfaces.                                                     *)
(* -------------------------------------------------------------------- *)

(* The adversary sees only Query. *)
module type QOracle = {
  proc query(x : D) : R
}.

(* The caller-chosen target is passed in (the adversary knows it) along    *)
(* with Initialize's output; the adversary then distinguishes with Query    *)
(* access.  Quantifying the lemma over every target captures the            *)
(* caller's free, non-adaptive choice. *)
module type Adv (O : QOracle) = {
  proc distinguish(target : D, r0 : R) : bool {O.query}
}.

(* The full game interface: Initialize is driven by the experiment, not   *)
(* the adversary. *)
module type RawRO = {
  proc initialize(target : D) : R
  proc query(x : D) : R
}.

(* Natural world: H is a lazy RO; Initialize returns H(target). *)
module NaturalO : RawRO = {
  var m   : (D, R) fmap
  var tgt : D            (* ghost: records the target for the proof only *)

  proc initialize(target : D) : R = {
    var y;
    m   <- empty;
    tgt <- target;
    y   <$ dR;
    m.[target] <- y;
    return y;
  }

  proc query(x : D) : R = {
    var r, y;
    if (x \notin m) {
      y <$ dR;
      m.[x] <- y;
    }
    r <- oget m.[x];
    return r;
  }
}.

(* Programmed world: Initialize returns a fresh u; Query answers u at the *)
(* target and the lazy RO elsewhere. *)
module ProgrammedO : RawRO = {
  var m : (D, R) fmap
  var t : D
  var u : R

  proc initialize(target : D) : R = {
    m <- empty;
    t <- target;
    u <$ dR;
    return u;
  }

  proc query(x : D) : R = {
    var r, y;
    if (x = t) {
      r <- u;
    } else {
      if (x \notin m) {
        y <$ dR;
        m.[x] <- y;
      }
      r <- oget m.[x];
    }
    return r;
  }
}.

(* The experiment: the caller picks the target, Initialize runs once, the *)
(* caller distinguishes with Query access. *)
module Exp (O : RawRO) (A : Adv) = {
  proc main(target : D) : bool = {
    var r0, b;
    r0 <@ O.initialize(target);
    b  <@ A(O).distinguish(target, r0);
    return b;
  }
}.

(* -------------------------------------------------------------------- *)
(* The advantage bound: perfect equivalence.                              *)
(* -------------------------------------------------------------------- *)

lemma adv_bound &m (A <: Adv {-NaturalO, -ProgrammedO}) (P : bool -> bool)
    (target : D) :
  Pr[Exp(NaturalO, A).main(target) @ &m : P res]
  = Pr[Exp(ProgrammedO, A).main(target) @ &m : P res].
proof.
byequiv (: ={glob A, target} ==> ={res}) => //.
proc.
call (:    NaturalO.tgt{1} = ProgrammedO.t{2}
        /\ NaturalO.m{1}.[NaturalO.tgt{1}] = Some ProgrammedO.u{2}
        /\ ProgrammedO.t{2} \notin ProgrammedO.m{2}
        /\ (forall z, z <> NaturalO.tgt{1} =>
              NaturalO.m{1}.[z] = ProgrammedO.m{2}.[z])).
+ (* Query preserves the reprogramming invariant. *)
  proc.
  if{2}.
  + (* x = t on the right: returns u. *)
    if{1}.
    + (* impossible: the target is always present in NaturalO.m. *)
      exfalso => &1 &2; smt(domE).
    + by wp; skip => /> &1 &2; smt(domE).
  + (* x <> t: both worlds read/lazily-sample the same coupled point. *)
    if.
    + by move=> &1 &2; smt(domE).
    + by wp; rnd; skip => /> &1 &2; smt(get_setE mem_set domE).
    + by wp; skip => /> &1 &2; smt(domE).
+ (* Initialize couples NaturalO's H(target) sample with ProgrammedO's u. *)
  inline NaturalO.initialize ProgrammedO.initialize.
  wp; rnd; wp; skip => />; smt(get_setE get_set_sameE emptyE mem_empty domE).
qed.
