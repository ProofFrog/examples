(* ==================================================================== *)
(* LazyROTwoViewsExcludedProgrammed: two-view lazy sampling with one      *)
(* programmed point                                                       *)
(*                                                                        *)
(* EasyCrypt proof of the ProofFrog statistical helper game pair in the    *)
(* co-located LazyROTwoViewsExcludedProgrammed.game.  This is the delta    *)
(* on LazyROTwoViewsExcluded.ec: the random oracle H : M -> R is exposed   *)
(* via the same two views Direct(m) / Indirect(q) (q = qExcluded -> None;  *)
(* else H(Pack(st, q))), but ONE distinguished input mProgrammed is        *)
(* programmed to a value yProgrammed that the GAME samples uniformly:      *)
(*                                                                        *)
(*   Honest.Initialize(st, qExc, mProg) : H = RF; return RF(mProg)        *)
(*   Honest.Direct(m)                   : return RF(m)                    *)
(*   Honest.Indirect(q)                 : return RF(Pack(st, q))          *)
(*   Lazy.Initialize(st, qExc, mProg)   : yProg <- R; return yProg        *)
(*   Lazy.Direct(m)     : m = mProg -> yProg ; else two-map lazy as 8e    *)
(*   Lazy.Indirect(q)   : Pack(st, q) = mProg -> yProg ; else as 8e       *)
(*                                                                        *)
(* The bound is 0: the two games are PERFECTLY indistinguishable for any   *)
(* caller-supplied (st, qExcluded, mProgrammed) and any predicate P.       *)
(* Honest's lazily sampled RF(mProgrammed) plays exactly the role of       *)
(* Lazy's separately-sampled yProgrammed (the classic one-point            *)
(* reprogramming fact, ROMProgramming.ec), grafted onto the two-view       *)
(* lazy-sampling equivalence of LazyROTwoViewsExcluded.ec.  As there, the  *)
(* equivalence is UNCONDITIONAL: by injectivity of Pack, an Indirect(q)    *)
(* entry can alias a Direct(m) entry only when m = Pack(st, q), and the    *)
(* Indirect priority branch routes a colliding query to yProgrammed        *)
(* exactly as Honest's RF(Pack(st, q)) = RF(mProgrammed) does.             *)
(*                                                                        *)
(* Proof shape.  A single byequiv with the 8e merged invariant plus the    *)
(* one-point coupling rf.[mProg] = Some yProg:                            *)
(*   (0) rf.[mProg] = Some yProg                                          *)
(*   (1) k \in ht  => rf.[k] = ht.[k]                                      *)
(*   (2) q \in qt  => rf.[Pack st q] = qt.[q]                             *)
(*   (3) k \in rf  => k = mProg \/ k \in ht                              *)
(*                              \/ exists q, q \in qt /\ Pack st q = k.    *)
(* ==================================================================== *)

require import AllCore FMap Distr.

(* The packing domain/codomain and the oracle codomain. *)
type state.
type query.
type M.
type R.

(* The injective hash-input packing P.Pack(st, .). *)
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

module type Views = {
  proc direct(m : M) : R
  proc indirect(q : query) : R option
}.

module type Game = {
  proc initialize(st0 : state, qExc0 : query, mProg0 : M) : R
  proc direct(m : M) : R
  proc indirect(q : query) : R option
}.

module type Adv (O : Views) = {
  proc distinguish(st0 : state, qExc0 : query, mProg0 : M, ss : R) : bool
    {O.direct, O.indirect}
}.

(* Honest: H is a single lazy RO rf; the programmed secret is RF(mProg). *)
module Honest : Game = {
  var st    : state
  var qExc  : query
  var mProg : M
  var rf    : (M, R) fmap

  proc initialize(st0 : state, qExc0 : query, mProg0 : M) : R = {
    var y;
    st    <- st0;
    qExc  <- qExc0;
    mProg <- mProg0;
    rf    <- empty;
    y     <$ dR;
    rf.[mProg0] <- y;
    return y;
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

(* Lazy: two cross-patched lazy maps; mProg routed to yProg in both views. *)
module Lazy : Game = {
  var st    : state
  var qExc  : query
  var mProg : M
  var yProg : R
  var ht    : (M, R) fmap
  var qt    : (query, R) fmap

  proc initialize(st0 : state, qExc0 : query, mProg0 : M) : R = {
    st    <- st0;
    qExc  <- qExc0;
    mProg <- mProg0;
    ht    <- empty;
    qt    <- empty;
    yProg <$ dR;
    return yProg;
  }

  proc direct(m : M) : R = {
    var r, oq;
    if (m = mProg) {
      r <- yProg;
    } else {
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
        if (m_in = mProg) {
          qt.[q] <- yProg;
          r  <- oget qt.[q];
          ro <- Some r;
        } else {
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
    }
    return ro;
  }
}.

module Exp (O : Game) (A : Adv) = {
  proc main(st0 : state, qExc0 : query, mProg0 : M) : bool = {
    var ss, b;
    ss <@ O.initialize(st0, qExc0, mProg0);
    b  <@ A(O).distinguish(st0, qExc0, mProg0, ss);
    return b;
  }
}.

(* -------------------------------------------------------------------- *)
(* The advantage bound: perfect equivalence.                              *)
(* -------------------------------------------------------------------- *)

lemma adv_bound &m (A <: Adv {-Honest, -Lazy}) (P : bool -> bool)
    (st0 : state) (qExc0 : query) (mProg0 : M) :
  Pr[Exp(Honest, A).main(st0, qExc0, mProg0) @ &m : P res]
  = Pr[Exp(Lazy, A).main(st0, qExc0, mProg0) @ &m : P res].
proof.
byequiv (: ={glob A, arg} ==> ={res}) => //.
proc.
call (:    Honest.st{1} = Lazy.st{2}
        /\ Honest.qExc{1} = Lazy.qExc{2}
        /\ Honest.mProg{1} = Lazy.mProg{2}
        /\ Honest.rf{1}.[Lazy.mProg{2}] = Some Lazy.yProg{2}
        /\ (forall k, k \in Lazy.ht{2} =>
              Honest.rf{1}.[k] = Lazy.ht{2}.[k])
        /\ (forall q, q \in Lazy.qt{2} =>
              Honest.rf{1}.[Pack Lazy.st{2} q] = Lazy.qt{2}.[q])
        /\ (forall k, k \in Honest.rf{1} =>
                 (k = Lazy.mProg{2})
              \/ (k \in Lazy.ht{2})
              \/ (exists q, q \in Lazy.qt{2} /\ Pack Lazy.st{2} q = k))).
+ (* Direct preserves the invariant. *)
  proc.
  if{2}.
  + (* m = mProg: Honest reads rf.[mProg] = yProg. *)
    if{1}.
    + by exfalso => &1 &2; smt(domE).
    + by wp; skip => /> &1 &2; smt(domE).
  + (* m <> mProg: exactly the 8e Direct. *)
    if{2}.
    + (* m \in ht *)
      if{1}.
      + by exfalso => &1 &2; smt(domE).
      + by wp; skip => /> &1 &2; smt(domE).
    + sp.
      if{2}.
      + (* oq <> None *)
        if{1}.
        + by exfalso => &1 &2; smt(find_not_none domE).
        + by wp; skip => /> &1 &2; smt(find_not_none get_setE domE).
      + (* oq = None: fresh *)
        if{1}.
        + wp; rnd; skip => /> &1 &2.
          have hnp := find_pack_none Lazy.st{2} m{2} Lazy.qt{2}.
          smt(get_setE mem_set domE).
        + exfalso => &1 &2.
          have hnp := find_pack_none Lazy.st{2} m{2} Lazy.qt{2}.
          smt(domE).
+ (* Indirect preserves the invariant. *)
  proc.
  if; first by move=> &1 &2; smt().
  + by auto.
  if{2}.
  + (* q \in qt *)
    sp 1 0.
    if{1}.
    + by exfalso => &1 &2; smt(domE).
    + by wp; skip => /> &1 &2; smt(domE).
  + sp 1 1.
    if{2}.
    + (* Pack st q = mProg: routed to yProg on both sides. *)
      if{1}.
      + by exfalso => &1 &2; smt(domE).
      + by wp; skip => /> &1 &2; smt(domE get_setE).
    + if{2}.
      + (* Pack st q \in ht *)
        if{1}.
        + by exfalso => &1 &2; smt(domE).
        + by wp; skip => /> &1 &2; smt(domE get_setE).
      + (* fresh on both sides *)
        if{1}.
        + by wp; rnd; skip => /> &1 &2; smt(domE get_setE mem_set Pack_inj).
        + by exfalso => &1 &2; smt(domE Pack_inj).
(* Initialize: programmed coupling RF(mProg) = yProg, empty maps. *)
inline *; auto => />; smt(get_set_sameE mem_set mem_empty emptyE).
qed.
