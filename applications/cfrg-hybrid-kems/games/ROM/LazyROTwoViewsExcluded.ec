(* ==================================================================== *)
(* LazyROTwoViewsExcluded: two-view lazy sampling of a random oracle      *)
(*                                                                        *)
(* EasyCrypt proof of the ProofFrog statistical helper game pair in the    *)
(* co-located LazyROTwoViewsExcluded.game:                                 *)
(*                                                                        *)
(*   H : BitString<P.M> -> BitString<n>, accessed via two views           *)
(*     Direct(m)   : returns H(m)                                         *)
(*     Indirect(q) : q = qExcluded -> None ; else returns H(Pack(st, q))  *)
(*   (the caller supplies an injective hash-input packing Pack(st, .)).    *)
(*                                                                        *)
(*   Honest : H = a random function rf; both views answer through rf.      *)
(*   Lazy   : two lazy maps ht (Direct) and qt (Indirect) cross-patched    *)
(*            via Pack; fresh entries sampled on demand, cross-view hits   *)
(*            routed through Pack.                                         *)
(*                                                                        *)
(* The bound is 0: the two games are PERFECTLY indistinguishable for any   *)
(* caller-supplied (st, qExcluded) and any predicate P on the output.      *)
(* Lazy's two cross-patched maps realise exactly one random oracle, viewed *)
(* directly at m and indirectly at Pack(st, q); the equivalence is         *)
(* UNCONDITIONAL because, by injectivity of Pack, an Indirect(q) entry can *)
(* alias a Direct(m) entry only when m = Pack(st, q).                      *)
(*                                                                        *)
(* Modeling notes.                                                        *)
(*  - The game-owned random function H : M -> R is modeled on the Honest   *)
(*    side as a lazily sampled finite map rf (modeling default #2); the    *)
(*    .game's eagerly sampled Function is observationally equivalent       *)
(*    through oracle access only.  The codomain needs only an arbitrary    *)
(*    distribution dR; neither uniformity nor losslessness is required     *)
(*    (every fresh sample is coupled one-one across the two worlds), which *)
(*    is why the bound is 0.                                               *)
(*  - Lazy is modeled FAITHFULLY with its two maps ht, qt.  The .game's     *)
(*    "scan ht.entries for a key equal to Pack(st, q)" is a direct M-keyed  *)
(*    lookup `Pack(st, q) \in ht`; the .game's "scan qt.entries for a query *)
(*    e whose Pack(st, e) equals m" is EasyCrypt's FMap.find over qt.       *)
(*  - The caller-chosen (st, qExcluded) are init parameters known to the    *)
(*    adversary (it picks them and then distinguishes via Direct/Indirect). *)
(*                                                                        *)
(* Proof shape.  A single byequiv with the merged invariant tying Honest's *)
(* one map rf to Lazy's two maps (ht, qt):                                 *)
(*   (1) k \in ht  => rf.[k] = ht.[k]                                      *)
(*   (2) q \in qt  => rf.[Pack st q] = qt.[q]                              *)
(*   (3) k \in rf  => k \in ht \/ exists q, q \in qt /\ Pack st q = k.     *)
(* Pack injectivity is used exactly in the fresh-miss branches to show     *)
(* that a never-before-seen point on one side is fresh on the other.       *)
(* ==================================================================== *)

require import AllCore FMap Distr.

(* The packing domain/codomain and the oracle codomain. *)
type state.
type query.
type M.
type R.

(* The injective hash-input packing P.Pack(st, .): for each fixed st,
   q |-> Pack st q is injective. *)
op Pack : state -> query -> M.
axiom Pack_inj (st : state) (q q' : query) :
  Pack st q = Pack st q' => q = q'.

(* The oracle output distribution (BitString<n> in the .game); arbitrary. *)
op dR : R distr.

(* find over qt returns None ==> no query in qt packs to mm. *)
lemma find_pack_none (st : state) (mm : M) (qt : (query, R) fmap) :
  find (fun (q : query) (_ : R) => Pack st q = mm) qt = None =>
  (forall q, q \in qt => Pack st q <> mm).
proof.
move=> hf q0 hq; apply/negP => hpack.
have heq : find (fun (q : query) (_ : R) => Pack st q = mm) qt = Some q0.
+ apply (uniq_find_eq_some q0).
  + move=> x y _ hpx; apply (Pack_inj st); by rewrite hpx hpack.
  + exact hq.
  + by rewrite /= hpack.
by move: heq; rewrite hf.
qed.

(* -------------------------------------------------------------------- *)
(* Module interfaces.                                                     *)
(* -------------------------------------------------------------------- *)

(* The adversary sees the two views. *)
module type Views = {
  proc direct(m : M) : R
  proc indirect(q : query) : R option
}.

(* The full game interface: Initialize is driven by the experiment. *)
module type Game = {
  proc initialize(st0 : state, qExc0 : query) : R
  proc direct(m : M) : R
  proc indirect(q : query) : R option
}.

(* The caller picks (st, qExcluded) and learns Initialize's output; it      *)
(* then distinguishes with Direct/Indirect access. *)
module type Adv (O : Views) = {
  proc distinguish(st0 : state, qExc0 : query, ss : R) : bool {O.direct, O.indirect}
}.

(* Honest: H is a single lazy RO rf; both views answer through it. *)
module Honest : Game = {
  var st   : state
  var qExc : query
  var rf   : (M, R) fmap

  proc initialize(st0 : state, qExc0 : query) : R = {
    var ss;
    st   <- st0;
    qExc <- qExc0;
    rf   <- empty;
    ss   <$ dR;
    return ss;
  }

  proc direct(m : M) : R = {
    var r;
    if (m \notin rf) {
      r <$ dR;
      rf.[m] <- r;
    }
    r <- oget rf.[m];
    return r;
  }

  proc indirect(q : query) : R option = {
    var r, m_in, ro;
    if (q = qExc) {
      ro <- None;
    } else {
      m_in <- Pack st q;
      if (m_in \notin rf) {
        r <$ dR;
        rf.[m_in] <- r;
      }
      r  <- oget rf.[m_in];
      ro <- Some r;
    }
    return ro;
  }
}.

(* Lazy: two cross-patched lazy maps ht (Direct), qt (Indirect). *)
module Lazy : Game = {
  var st   : state
  var qExc : query
  var ht   : (M, R) fmap
  var qt   : (query, R) fmap

  proc initialize(st0 : state, qExc0 : query) : R = {
    var ss;
    st   <- st0;
    qExc <- qExc0;
    ht   <- empty;
    qt   <- empty;
    ss   <$ dR;
    return ss;
  }

  proc direct(m : M) : R = {
    var r, oq;
    if (m \in ht) {
      r <- oget ht.[m];
    } else {
      oq <- find (fun (q : query) (_ : R) => Pack st q = m) qt;
      if (oq <> None) {
        ht.[m] <- oget qt.[oget oq];
        r <- oget ht.[m];
      } else {
        r <$ dR;
        ht.[m] <- r;
      }
    }
    return r;
  }

  proc indirect(q : query) : R option = {
    var r, m_in, ro;
    if (q = qExc) {
      ro <- None;
    } else {
      if (q \in qt) {
        r  <- oget qt.[q];
        ro <- Some r;
      } else {
        m_in <- Pack st q;
        if (m_in \in ht) {
          qt.[q] <- oget ht.[m_in];
          r  <- oget qt.[q];
          ro <- Some r;
        } else {
          r <$ dR;
          qt.[q] <- r;
          ro <- Some r;
        }
      }
    }
    return ro;
  }
}.

(* The experiment: the caller picks (st, qExcluded), Initialize runs once,  *)
(* the caller distinguishes with Direct/Indirect access. *)
module Exp (O : Game) (A : Adv) = {
  proc main(st0 : state, qExc0 : query) : bool = {
    var ss, b;
    ss <@ O.initialize(st0, qExc0);
    b  <@ A(O).distinguish(st0, qExc0, ss);
    return b;
  }
}.

(* -------------------------------------------------------------------- *)
(* The advantage bound: perfect equivalence.                              *)
(* -------------------------------------------------------------------- *)

lemma adv_bound &m (A <: Adv {-Honest, -Lazy}) (P : bool -> bool)
    (st0 : state) (qExc0 : query) :
  Pr[Exp(Honest, A).main(st0, qExc0) @ &m : P res]
  = Pr[Exp(Lazy, A).main(st0, qExc0) @ &m : P res].
proof.
byequiv (: ={glob A, arg} ==> ={res}) => //.
proc.
call (:    Honest.st{1} = Lazy.st{2}
        /\ Honest.qExc{1} = Lazy.qExc{2}
        /\ (forall k, k \in Lazy.ht{2} =>
              Honest.rf{1}.[k] = Lazy.ht{2}.[k])
        /\ (forall q, q \in Lazy.qt{2} =>
              Honest.rf{1}.[Pack Lazy.st{2} q] = Lazy.qt{2}.[q])
        /\ (forall k, k \in Honest.rf{1} =>
                 (k \in Lazy.ht{2})
              \/ (exists q, q \in Lazy.qt{2} /\ Pack Lazy.st{2} q = k))).
+ (* Direct preserves the invariant. *)
  proc.
  if{2}.
  + (* m \in ht{2}: Honest already has m. *)
    if{1}.
    + by exfalso => &1 &2; smt(domE).
    + by wp; skip => /> &1 &2; smt(domE).
  + sp.
    if{2}.
    + (* oq <> None: m is a packed query point, already in Honest.rf. *)
      if{1}.
      + by exfalso => &1 &2; smt(find_not_none domE).
      + by wp; skip => /> &1 &2; smt(find_not_none get_setE domE).
    + (* oq = None: m is fresh on both sides. *)
      if{1}.
      + by wp; rnd; skip => /> &1 &2; smt(find_pack_none get_setE mem_set domE).
      + by exfalso => &1 &2; smt(find_pack_none domE).
+ (* Indirect preserves the invariant. *)
  proc.
  if; first by move=> &1 &2; smt().
  + by auto.
  if{2}.
  + (* q \in qt{2}: Honest already has Pack st q. *)
    sp 1 0.
    if{1}.
    + by exfalso => &1 &2; smt(domE).
    + by wp; skip => /> &1 &2; smt(domE).
  + sp 1 1.
    if{2}.
    + (* Pack st q \in ht{2}: Honest already has it. *)
      if{1}.
      + by exfalso => &1 &2; smt(domE).
      + by wp; skip => /> &1 &2; smt(domE get_setE).
    + (* fresh on both sides. *)
      if{1}.
      + by wp; rnd; skip => /> &1 &2; smt(domE get_setE mem_set Pack_inj).
      + by exfalso => &1 &2; smt(domE Pack_inj).
(* Initialize: both empty the maps and return a coupled fresh sample. *)
inline *; auto => />; smt(mem_empty emptyE).
qed.
