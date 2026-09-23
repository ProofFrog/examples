(* ==================================================================== *)
(* OAEPExtractStatFlag: the OAEP plaintext extractor agrees with real     *)
(* decryption unless a rare event occurs (FOPS 2001, decryption lemma)    *)
(*                                                                        *)
(* EasyCrypt proof of the ProofFrog flag game in the co-located            *)
(* OAEPExtractStatFlag.game (the Right side of OAEPExtractStat plus a      *)
(* Reveal oracle), whose declared clause is (lemma adv_bound, op bound)    *)
(*                                                                        *)
(*   adv <= count_Dec * ((5 count_HashG + count_Dec + 1) / 2^k0           *)
(*                       + count_HashH / 2^(n + k1) + 1 / 2^k1).          *)
(*                                                                        *)
(* Proof outline (section PROOF, one lemma per hop):                      *)
(*  - pr_real_ideal: Real <= Ideal + Pr[Ideal : bad] (up-to-bad).         *)
(*  - pr_E0_G1 .. pr_guess_E3: guess the index i of the first Dec query   *)
(*    that raises bad (PlugAndPray; factor max 1 qD) and compute bad only  *)
(*    there.                                                              *)
(*  - pr_E3_E3c: freeze the game once bad is decided (askH, the i-th Dec  *)
(*    query) or when the challenge's sStar was already H-queried (preH);   *)
(*    pr_E3c_preH bounds preH by (qG + qD)/2^k0 + qH/2^(n+k1).            *)
(*  - pr_E3c_F3a .. pr_F3b_LRO: the RO values fixed by earlier Dec queries *)
(*    become PROM `sample`s and disappear (lazy/eager, RO_LRO_D).          *)
(*  - pr_E3L_O4 .. pr_F4_LRO: the challenge samples tStar fresh and rStar  *)
(*    is recomputed from H(sStar) at the end (change of variables), so     *)
(*    bad becomes a union of events on fresh samples (badG).              *)
(*  - fel_dec, fel_chal, pr_E5: failure-event lemmas on the final game:   *)
(*    2qG/2^k0 + 1/2^k1 (the i-th Dec query), qG/2^k0 (challenge),        *)
(*    (qG + 1)/2^k0 (the final rStar recomputation).                      *)
(*  - pr_bad, adv_bound: assembly; qD = 0 is handled separately (no Dec    *)
(*    query, so bad is never raised).                                     *)
(*                                                                        *)
(* Modeling notes.                                                        *)
(*  - BitString<n + k1> (G's outputs, H's inputs, the s-half) is modeled  *)
(*    as the product ptxt * red of a plaintext and the k1-bit redundancy  *)
(*    block, with componentwise XOR (ZModule); BitString<k0> (H's         *)
(*    outputs, G's inputs, the t-half) is the ZModule htag.  Then         *)
(*    m || 0^k1 is pad m = (m, zero) and the padding check p[n:n+k1] = 0  *)
(*    is unpad p <> None, and a fresh uniform gtag passes it with          *)
(*    probability 1/|red| (no axiom needed).                              *)
(*  - The trapdoor permutation is abstract: f pk and fi sk cancel on the  *)
(*    key support (as in EasyCrypt's examples/incomplete/oaep/OAEP.eca).  *)
(*  - The random oracles G and H are lazily sampled maps; the adversary's *)
(*    queries are additionally LOGGED in lists, and the extractor scans   *)
(*    the logs (the .game's GT / HT tables), not the oracle domains.      *)
(*  - The extractor is the list search extract2 (ported from OAEP.eca).   *)
(*  - Query budgets qD (Dec), qG (HashG) and qH (HashH) are enforced by   *)
(*    the experiment wrapper, as in the other helper proofs.              *)
(* ==================================================================== *)

require import AllCore List FSet FMap Distr DProd StdOrder StdBigop.
(*---*) import RealOrder Bigreal BRA.
require import Mu_mem FelTactic.
require (*--*) Ring PROM PlugAndPray.

(* -------------------------------------------------------------------- *)
(* Plaintexts, redundancy block, tags.                                    *)
(* -------------------------------------------------------------------- *)

type ptxt.
clone import Ring.ZModule as Ptxt with type t <- ptxt.
clone import MFinite as FinPtxt with type t <- ptxt.

type red.
clone import Ring.ZModule as Red with type t <- red.
clone import MFinite as FinRed with type t <- red.

type htag.
clone import Ring.ZModule as HTag with type t <- htag.
clone import MFinite as FinHtag with type t <- htag.

(* gtag = ptxt * red with componentwise XOR *)
type gtag = ptxt * red.

op gadd (x y : gtag) : gtag = (x.`1 + y.`1, x.`2 + y.`2).
op gopp (x : gtag) : gtag = (- x.`1, - x.`2).
op gzero : gtag = (Ptxt.zeror, Red.zeror).
(* XOR is its own inverse; in the general ZModule model, decryption removes a
   mask with subtraction so no characteristic-2 axiom is needed. *)
op gsub (x y : gtag) : gtag = gadd x (gopp y).

clone import Ring.ZModule as GTag with
  type t     <- gtag,
  op   zeror <- gzero,
  op   (+)   <- gadd,
  op   [-]   <- gopp
proof *.
realize addrA. by move=> x y z; rewrite /gadd /= Ptxt.addrA Red.addrA. qed.
realize addrC. by move=> x y; rewrite /gadd /= Ptxt.addrC Red.addrC. qed.
realize add0r. by move=> [x1 x2]; rewrite /gadd /gzero /= Ptxt.add0r Red.add0r. qed.
realize addNr. by move=> [x1 x2]; rewrite /gadd /gopp /gzero /= Ptxt.addNr Red.addNr. qed.

op dptxt : ptxt distr = FinPtxt.dunifin.
op dred  : red  distr = FinRed.dunifin.
op dhtag : htag distr = FinHtag.dunifin.
op dgtag : gtag distr = dptxt `*` dred.

op cardRed  : int = FinRed.Support.card.
op cardHtag : int = FinHtag.Support.card.

lemma dgtag_ll : is_lossless dgtag.
proof. by rewrite dprod_ll FinPtxt.dunifin_ll FinRed.dunifin_ll. qed.

lemma dhtag_ll : is_lossless dhtag.
proof. exact FinHtag.dunifin_ll. qed.

lemma cardRed_gt0 : 0 < cardRed.
proof. exact FinRed.Support.card_gt0. qed.

lemma cardHtag_gt0 : 0 < cardHtag.
proof. exact FinHtag.Support.card_gt0. qed.

lemma mu_dhtag_mem (X : htag fset) : mu dhtag (mem X) <= (card X)%r / cardHtag%r.
proof.
have -> : (card X)%r / cardHtag%r = (card X)%r * (1%r / cardHtag%r) by smt().
apply (mu_mem_le X dhtag (1%r / cardHtag%r)).
by move=> x _; rewrite FinHtag.dunifin1E.
qed.

(* padding *)
op pad (m : ptxt) : gtag = (m, Red.zeror).
op unpad (x : gtag) : ptxt option = if x.`2 = Red.zeror then Some x.`1 else None.

lemma padK m : unpad (pad m) = Some m.
proof. by rewrite /pad /unpad. qed.

lemma unpad_some x m : unpad x = Some m => x = pad m.
proof.
rewrite /unpad /pad; case: (x.`2 = Red.zeror) => hz //=.
by move=> <-; smt().
qed.

(* A fresh uniform gtag passes the padding check with probability 1/|red|. *)
lemma mu_dgtag_valid : mu dgtag (fun x => unpad x <> None) = 1%r / cardRed%r.
proof.
rewrite /dgtag.
have -> : (fun (x : gtag) => unpad x <> None)
          = (fun (x : gtag) => predT x.`1 /\ pred1 Red.zeror x.`2).
+ by apply fun_ext => x; rewrite /unpad /predT /pred1 /=; case: (x.`2 = Red.zeror).
rewrite (dprodE predT (pred1 Red.zeror) dptxt dred).
by rewrite FinPtxt.dunifin_ll FinRed.dunifin1E /cardRed.
qed.

(* The uniform distribution on gtag: point mass and invariance under
   bijections (translations). *)
op cardGtag : int = FinPtxt.Support.card * cardRed.

lemma div_le (a b c : real) : 0%r < c => a <= b => a / c <= b / c.
proof. by move=> hc hab; apply ler_wpmul2r; smt(invr_ge0). qed.

lemma cardGtag_gt0 : 0 < cardGtag.
proof. by rewrite /cardGtag; smt(FinPtxt.Support.card_gt0 cardRed_gt0). qed.

lemma dgtag1E (x : gtag) : mu1 dgtag x = 1%r / cardGtag%r.
proof.
case: x => a b; rewrite /dgtag dprod1E FinPtxt.dunifin1E FinRed.dunifin1E /cardGtag /cardRed.
by rewrite fromintM; field; smt(FinPtxt.Support.card_gt0 FinRed.Support.card_gt0).
qed.

lemma dgtag_bij (f g : gtag -> gtag) (P : gtag -> bool) :
  cancel f g => cancel g f =>
  mu dgtag (fun y => P (f y)) = mu dgtag P.
proof.
move=> hfg hgf.
have -> : (fun y => P (f y)) = P \o f by done.
rewrite -dmapE; congr; apply eq_distr => x.
rewrite dmap1E /(\o).
have -> : (fun y => pred1 x (f y)) = pred1 (g x).
+ by apply fun_ext => y; rewrite /pred1; smt().
by rewrite !dgtag1E.
qed.

lemma gsubK (s : gtag) : cancel (gsub s) (gsub s).
proof. by move=> x; rewrite /gsub; smt(@GTag). qed.

lemma gaddK (a : gtag) : cancel (gadd a) (fun x => gsub x a).
proof. by move=> x; rewrite /gsub; smt(@GTag). qed.

lemma gaddKV (a : gtag) : cancel (fun x => gsub x a) (gadd a).
proof. by move=> x; rewrite /gsub; smt(@GTag). qed.

lemma mu_dgtag_valid_sub (s : gtag) :
  mu dgtag (fun g => unpad (gsub s g) <> None) = 1%r / cardRed%r.
proof.
by rewrite (dgtag_bij (gsub s) (gsub s) (fun x => unpad x <> None) (gsubK s) (gsubK s)) mu_dgtag_valid.
qed.

lemma mu_dgtag_mem_shift (a : gtag) (L : gtag list) :
  mu dgtag (fun g => gadd a g \in L) <= (size L)%r / cardGtag%r.
proof.
rewrite (dgtag_bij (gadd a) (fun x => gsub x a) (mem L) (gaddK a) (gaddKV a)).
have -> : (size L)%r / cardGtag%r = (size L)%r * (1%r / cardGtag%r) by smt().
by apply (mu_mem_le_mu1 dgtag L (1%r / cardGtag%r)) => x; rewrite dgtag1E.
qed.

lemma mu_dhtag_fdom (m : (htag, 'b) fmap) :
  mu dhtag (fun r => r \in m) <= (fsize m)%r / cardHtag%r.
proof.
have -> : (fun r => r \in m) = mem (fdom m) by apply fun_ext => r; rewrite mem_fdom.
by rewrite /fsize; apply mu_dhtag_mem.
qed.

lemma dhtag1E (x : htag) : mu1 dhtag x = 1%r / cardHtag%r.
proof. by rewrite /dhtag FinHtag.dunifin1E. qed.

lemma dhtag_bij (f g : htag -> htag) (P : htag -> bool) :
  cancel f g => cancel g f =>
  mu dhtag (fun y => P (f y)) = mu dhtag P.
proof.
move=> hfg hgf.
have -> : (fun y => P (f y)) = P \o f by done.
rewrite -dmapE; congr; apply eq_distr => x.
rewrite dmap1E /(\o).
have -> : (fun y => pred1 x (f y)) = pred1 (g x).
+ by apply fun_ext => y; rewrite /pred1; smt().
by rewrite !dhtag1E.
qed.

(* Pr[ t - h in L ] for a fresh h *)
lemma mu_dhtag_mem_sub (t : htag) (L : htag list) :
  mu dhtag (fun h => t - h \in L) <= (size L)%r / cardHtag%r.
proof.
rewrite (dhtag_bij (fun h => t - h) (fun h => t - h) (mem L)).
+ by move=> h; smt(@HTag).
+ by move=> h; smt(@HTag).
have -> : (size L)%r / cardHtag%r = (size L)%r * (1%r / cardHtag%r) by smt().
by apply (mu_mem_le_mu1 dhtag L (1%r / cardHtag%r)) => x; rewrite dhtag1E.
qed.

(* Pr[ t - h in L ] for a fresh h, where t - h uses the OTHER argument order *)
lemma mu_dhtag_mem_sub' (t : htag) (L : htag list) :
  mu dhtag (fun h => h - t \in L) <= (size L)%r / cardHtag%r.
proof.
rewrite (dhtag_bij (fun h => h - t) (fun h => h + t) (mem L)).
+ by move=> h; smt(@HTag).
+ by move=> h; smt(@HTag).
have -> : (size L)%r / cardHtag%r = (size L)%r * (1%r / cardHtag%r) by smt().
by apply (mu_mem_le_mu1 dhtag L (1%r / cardHtag%r)) => x; rewrite dhtag1E.
qed.

(* -------------------------------------------------------------------- *)
(* The trapdoor permutation on gtag * htag.                               *)
(* -------------------------------------------------------------------- *)

type pkey, skey.

op dkeys : { (pkey * skey) distr | is_lossless dkeys } as dkeys_ll.

op f  : pkey -> gtag * htag -> gtag * htag.
op fi : skey -> gtag * htag -> gtag * htag.

axiom fK  pk sk : (pk, sk) \in dkeys => cancel (f pk) (fi sk).
axiom fiK pk sk : (pk, sk) \in dkeys => cancel (fi sk) (f pk).

(* query budgets *)
op qD : { int | 0 <= qD } as qD_ge0.
op qG : { int | 0 <= qG } as qG_ge0.
op qH : { int | 0 <= qH } as qH_ge0.

(* -------------------------------------------------------------------- *)
(* The plaintext extractor: scan the H log and the G log for an (s, r)   *)
(* whose image is the ciphertext and whose padding checks.               *)
(* -------------------------------------------------------------------- *)

op extract (p : 'x -> bool) (xs : 'x list) : 'x option =
  with xs = []      => None
  with xs = x :: xs => if p x then Some x else extract p xs.

op extract2 (p : 'x -> 'y -> bool) (xs : 'x list) (ys : 'y list) : ('x * 'y) option =
  with xs = []      => None
  with xs = x :: xs =>
    let y = extract (p x) ys in
    if y <> None then Some (x, oget y) else extract2 p xs ys.

lemma extract_correct (p : 'x -> bool) xs a :
  extract p xs = Some a => p a /\ a \in xs.
proof.
elim: xs => //= x xs ih; case: (p x) => hpx /=.
+ by move=> <-.
by move=> /ih [-> hin] /=; right.
qed.

lemma extract_exists (p : 'x -> bool) xs a :
  a \in xs => p a => extract p xs <> None.
proof.
elim: xs => //= x xs ih [-> | hin] hpa; case: (p x) => //= hpx; exact (ih hin hpa).
qed.

lemma extract2_correct (p : 'x -> 'y -> bool) xs ys a b :
  extract2 p xs ys = Some (a, b) => p a b /\ a \in xs /\ b \in ys.
proof.
elim: xs => //= x xs ih; case: (extract (p x) ys = None) => hex /=.
+ by move=> /ih [hp [hin hb]]; do !split => //; right.
move=> [<- <-].
case: {-1}(extract (p x) ys) (eq_refl (extract (p x) ys)) hex => [hnone hne | y hy _].
+ by [].
by have := extract_correct (p x) ys y hy; smt().
qed.

lemma extract2_exists (p : 'x -> 'y -> bool) xs ys a b :
  a \in xs => b \in ys => p a b => extract2 p xs ys <> None.
proof.
elim: xs => //= x xs ih [-> | hin] hb hp.
+ by have := extract_exists (p x) ys b hb hp; case: (extract (p x) ys).
by case: (extract (p x) ys) => //=; exact (ih hin hb hp).
qed.

(* the extractor as used by Dec: the message of the first match, if any *)
op ext (pk : pkey) (lh : (gtag * htag) list) (lg : (htag * gtag) list)
       (c : gtag * htag) : ptxt option =
  let m = extract2 (fun (sh : gtag * htag) (rg : htag * gtag) =>
                      c = f pk (sh.`1, rg.`1 + sh.`2) /\ unpad (gsub sh.`1 rg.`2) <> None)
                   lh lg in
  if m = None then None else unpad (gsub (oget m).`1.`1 (oget m).`2.`2).

(* -------------------------------------------------------------------- *)
(* Extractor soundness.  When the logs agree with the oracle maps, the    *)
(* extractor's answer, if any, is the real decryption's, and it has an    *)
(* answer as soon as both the real s and the real r were queried.         *)
(* -------------------------------------------------------------------- *)

pred logs_okH (lh : (gtag * htag) list) (hm : (gtag, htag) fmap) =
  forall x y, (x, y) \in lh => hm.[x] = Some y.

pred logs_okG (lg : (htag * gtag) list) (gm : (htag, gtag) fmap) =
  forall x y, (x, y) \in lg => gm.[x] = Some y.

lemma ext_sound pk sk lh lg hm gm c :
  (pk, sk) \in dkeys => logs_okH lh hm => logs_okG lg gm =>
  (fi sk c).`1 \in hm => (((fi sk c).`2 - oget hm.[(fi sk c).`1])) \in gm =>
  ext pk lh lg c <> None =>
  ext pk lh lg c
  = unpad (gsub (fi sk c).`1
                (oget gm.[(fi sk c).`2 - oget hm.[(fi sk c).`1]])).
proof.
move=> hk hlh hlg hs hr; rewrite /ext /=.
pose P := (fun (sh : gtag * htag) (rg : htag * gtag) => c = f pk (sh.`1, rg.`1 + sh.`2) /\ unpad (gsub sh.`1 rg.`2) <> None); case: {-1}(extract2 P lh lg) (eq_refl (extract2 P lh lg)) => [| [sh rg]] //= hex.
have [[hc hu] [hsh hrg]] := extract2_correct P lh lg sh rg hex; have hfi : fi sk c = (sh.`1, rg.`1 + sh.`2) by rewrite hc (fK pk sk hk).
rewrite hfi /=; have -> : hm.[sh.`1] = Some sh.`2 by have := hlh sh.`1 sh.`2; smt().
by rewrite oget_some HTag.addrK; have -> : gm.[rg.`1] = Some rg.`2 by have := hlg rg.`1 rg.`2; smt().
qed.

lemma ext_complete pk sk lh lg hm gm c :
  (pk, sk) \in dkeys => logs_okH lh hm => logs_okG lg gm =>
  (exists y, ((fi sk c).`1, y) \in lh) =>
  (exists y, ((fi sk c).`2 - oget hm.[(fi sk c).`1], y) \in lg) =>
  unpad (gsub (fi sk c).`1
              (oget gm.[(fi sk c).`2 - oget hm.[(fi sk c).`1]])) <> None =>
  ext pk lh lg c <> None.
proof.
move=> hk hlh hlg [y hy] [g hg]; have hy' : hm.[(fi sk c).`1] = Some y by apply hlh.
move: hg; rewrite hy' oget_some => hg; have hg' : gm.[(fi sk c).`2 - y] = Some g by apply hlg.
rewrite hg' oget_some => hu; rewrite /ext /=.
pose P := fun (sh : gtag * htag) (rg : htag * gtag) =>
  c = f pk (sh.`1, rg.`1 + sh.`2) /\ unpad (gsub sh.`1 rg.`2) <> None.
have hP : P ((fi sk c).`1, y) ((fi sk c).`2 - y, g).
+ rewrite /P /= HTag.subrK; split => //.
  by have := fiK pk sk hk c; case: (fi sk c) => s t /= <-.
have hne := extract2_exists P lh lg _ _ hy hg hP.
case: {-1}(extract2 P lh lg) (eq_refl (extract2 P lh lg)) hne => [| [sh rg]] //= hex.
by have [[_ hu'] _] := extract2_correct P lh lg sh rg hex.
qed.

lemma in_unzip1 ['a 'b] (x : 'a) (l : ('a * 'b) list) :
  x \in unzip1 l => exists y, (x, y) \in l.
proof. by rewrite mapP => -[[a b] [hin ->]]; exists b. qed.

(* When both the real s and the real r were logged, the extractor's answer
   IS the real decryption. *)
lemma ext_logged pk sk lh lg hm gm c :
  (pk, sk) \in dkeys => logs_okH lh hm => logs_okG lg gm =>
  (fi sk c).`1 \in unzip1 lh =>
  ((fi sk c).`2 - oget hm.[(fi sk c).`1]) \in unzip1 lg =>
  ext pk lh lg c
  = unpad (gsub (fi sk c).`1 (oget gm.[(fi sk c).`2 - oget hm.[(fi sk c).`1]])).
proof.
move=> hk hlh hlg /in_unzip1 [y hy] /in_unzip1 [g hg].
have hs : (fi sk c).`1 \in hm by have := hlh _ _ hy; smt(domE).
have hr : ((fi sk c).`2 - oget hm.[(fi sk c).`1]) \in gm by have := hlg _ _ hg; smt(domE).
case: (unpad (gsub (fi sk c).`1 (oget gm.[(fi sk c).`2 - oget hm.[(fi sk c).`1]])) = None) => hu.
+ rewrite hu; case: (ext pk lh lg c = None) => // hne.
  by have := ext_sound pk sk lh lg hm gm c hk hlh hlg hs hr hne; rewrite hu.
have hne : ext pk lh lg c <> None.
+ by apply (ext_complete pk sk lh lg hm gm c hk hlh hlg); [exists y | exists g | ].
exact (ext_sound pk sk lh lg hm gm c hk hlh hlg hs hr hne).
qed.

(* In general the extractor either has no answer or the real one. *)
lemma ext_cases pk sk lh lg hm gm c :
  (pk, sk) \in dkeys => logs_okH lh hm => logs_okG lg gm =>
  (fi sk c).`1 \in hm => ((fi sk c).`2 - oget hm.[(fi sk c).`1]) \in gm =>
  ext pk lh lg c = None \/
  ext pk lh lg c
  = unpad (gsub (fi sk c).`1 (oget gm.[(fi sk c).`2 - oget hm.[(fi sk c).`1]])).
proof.
move=> hk hlh hlg hs hr; case: (ext pk lh lg c = None) => [-> // | hne]; right.
exact (ext_sound pk sk lh lg hm gm c hk hlh hlg hs hr hne).
qed.

(* -------------------------------------------------------------------- *)
(* The random oracles G : htag -> gtag and H : gtag -> htag (PROM).        *)
(* -------------------------------------------------------------------- *)

clone import PROM.FullRO as GRO with
  type in_t    <- htag,
  type out_t   <- gtag,
  type d_in_t  <- unit,
  type d_out_t <- bool,
  op   dout    <- fun (_ : htag) => dgtag
proof *.

clone import PROM.FullRO as HRO with
  type in_t    <- gtag,
  type out_t   <- htag,
  type d_in_t  <- unit,
  type d_out_t <- bool,
  op   dout    <- fun (_ : gtag) => dhtag
proof *.

(* -------------------------------------------------------------------- *)
(* Module interfaces.                                                     *)
(* -------------------------------------------------------------------- *)

module type Oracles = {
  proc hashG(x : htag) : gtag
  proc hashH(x : gtag) : htag
  proc challenge(m : ptxt) : (gtag * htag) option
  proc inS(c : gtag * htag) : bool
  proc dec(c : gtag * htag) : ptxt option
  proc reveal() : bool
}.

module type Adv (O : Oracles) = {
  proc run() : bool { O.hashG, O.hashH, O.challenge, O.inS, O.dec, O.reveal }
}.

(* Shared game state (the oracle tables live in GRO.RO.m / HRO.RO.m). *)
module Mem = {
  var logG : (htag * gtag) list    (* the adversary's G queries (GT) *)
  var logH : (gtag * htag) list    (* the adversary's H queries (HT) *)
  var pk   : pkey
  var sk   : skey
  var cS   : (gtag * htag) option  (* the challenge ciphertext, if any (S) *)
  var sStar : gtag
  var challenged : bool
  var askH : bool
  var bad  : bool
}.

(* The flag game's oracles (OAEPExtractStat.Right); reveal is the only
   difference between Real (returns bad) and Ideal (returns false). *)
module type RawG = {
  proc init() : unit
  proc fhashG(x : htag) : gtag
  proc fhashH(x : gtag) : htag
  proc fchallenge(m : ptxt) : (gtag * htag) option
  proc finS(c : gtag * htag) : bool
  proc fdec(c : gtag * htag) : ptxt option
  proc freveal() : bool
}.

module RealO : RawG = {
  proc init() : unit = {
    (Mem.pk, Mem.sk) <$ dkeys;
    GRO.RO.init();
    HRO.RO.init();
    Mem.logG <- [];
    Mem.logH <- [];
    Mem.cS   <- None;
    Mem.sStar <- gzero;
    Mem.challenged <- false;
    Mem.askH <- false;
    Mem.bad  <- false;
  }

  proc fhashG(x : htag) : gtag = {
    var y;
    y <@ GRO.RO.get(x);
    Mem.logG <- (x, y) :: Mem.logG;
    return y;
  }

  proc fhashH(x : gtag) : htag = {
    var y;
    if (Mem.challenged /\ x = Mem.sStar) {
      Mem.askH <- true;
    }
    y <@ HRO.RO.get(x);
    Mem.logH <- (x, y) :: Mem.logH;
    return y;
  }

  proc fchallenge(m : ptxt) : (gtag * htag) option = {
    var r, s, t, c, result;
    result <- None;
    if (Mem.cS = None) {
      r <$ dhtag;
      s <@ GRO.RO.get(r);
      s <- gadd (pad m) s;
      t <@ HRO.RO.get(s);
      t <- r + t;
      c <- f Mem.pk (s, t);
      Mem.cS <- Some c;
      Mem.sStar <- s;
      Mem.challenged <- true;
      result <- Some c;
    }
    return result;
  }

  proc finS(c : gtag * htag) : bool = {
    return Mem.cS = Some c;
  }

  (* Real decryption AND the extractor; the flag is raised on a
     disagreement while H has not been queried at sStar; the extractor's
     answer is returned (this is the pair's Right side). *)
  proc fdec(c : gtag * htag) : ptxt option = {
    var s, t, r, g, p, mExt, m, result;
    result <- None;
    if (Mem.cS <> Some c) {
      (s, t) <- fi Mem.sk c;
      r <@ HRO.RO.get(s);
      r <- t - r;
      g <@ GRO.RO.get(r);
      p <- gsub s g;
      mExt <- ext Mem.pk Mem.logH Mem.logG c;
      if (unpad p <> None) {
        m <- oget (unpad p);
        if (!Mem.askH) {
          if (mExt <> Some m) {
            Mem.bad <- true;
          }
        }
      } else {
        if (!Mem.askH) {
          if (mExt <> None) {
            Mem.bad <- true;
          }
        }
      }
      result <- if Mem.askH then unpad p else mExt;
    }
    return result;
  }

  proc freveal() : bool = {
    return Mem.bad;
  }
}.

module IdealO : RawG = {
  proc init       = RealO.init
  proc fhashG     = RealO.fhashG
  proc fhashH     = RealO.fhashH
  proc fchallenge = RealO.fchallenge
  proc finS       = RealO.finS
  proc fdec       = RealO.fdec

  proc freveal() : bool = {
    return false;
  }
}.

(* The bounded-query experiment: at most qD Dec, qG HashG, qH HashH calls. *)
module Exp (O : RawG) (A : Adv) = {
  module WO : Oracles = {
    var cD : int
    var cG : int
    var cH : int

    proc init() : unit = {
      cD <- 0;
      cG <- 0;
      cH <- 0;
      O.init();
    }

    proc hashG(x : htag) : gtag = {
      var r;
      r <- witness;
      if (cG < qG) {
        r  <@ O.fhashG(x);
        cG <- cG + 1;
      }
      return r;
    }

    proc hashH(x : gtag) : htag = {
      var r;
      r <- witness;
      if (cH < qH) {
        r  <@ O.fhashH(x);
        cH <- cH + 1;
      }
      return r;
    }

    proc challenge(m : ptxt) : (gtag * htag) option = {
      var r;
      r <@ O.fchallenge(m);
      return r;
    }

    proc inS(c : gtag * htag) : bool = {
      var r;
      r <@ O.finS(c);
      return r;
    }

    proc dec(c : gtag * htag) : ptxt option = {
      var r;
      r <- None;
      if (cD < qD) {
        r  <@ O.fdec(c);
        cD <- cD + 1;
      }
      return r;
    }

    proc reveal() : bool = {
      var r;
      r <@ O.freveal();
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

(* -------------------------------------------------------------------- *)
(* The advantage bound.                                                   *)
(* -------------------------------------------------------------------- *)

(* The statistical bound established below (see the .game header for the
   clause and the reason for the count_HashH term). *)
op bound : real =
  qD%r * ((5 * qG + qD + 1)%r / cardHtag%r + qH%r / cardGtag%r + 1%r / cardRed%r).

section PROOF.

declare module A <: Adv {-Mem, -Exp, -GRO.RO, -GRO.FRO, -HRO.RO, -HRO.FRO}.

declare axiom A_ll :
  forall (O <: Oracles {-A}),
    islossless O.hashG => islossless O.hashH => islossless O.challenge =>
    islossless O.inS => islossless O.dec => islossless O.reveal =>
    islossless A(O).run.

(* Step 1: Real is identical to Ideal until bad (they differ only in
   reveal), so any predicate on the output is bounded by Pr[bad]. *)
local lemma pr_real_ideal &m (P : bool -> bool) :
  Pr[Exp(RealO, A).main() @ &m : P res]
  <= Pr[Exp(IdealO, A).main() @ &m : P res] + Pr[Exp(IdealO, A).main() @ &m : Mem.bad].
proof.
apply (ler_trans Pr[Exp(IdealO, A).main() @ &m : P res \/ Mem.bad]); last by rewrite Pr [mu_or]; smt(ge0_mu).
byequiv (: ={glob A} ==> !Mem.bad{2} => ={res}) => //; last by smt().
proc; call (: Mem.bad, ={glob Mem, glob GRO.RO, glob HRO.RO, Exp.WO.cD, Exp.WO.cG, Exp.WO.cH}, true).
+ exact A_ll.
+ by proc; sim.
+ move=> &2 _; proc; sp; if => //; inline *; auto => />; smt(dgtag_ll).
+ move=> &2; proc; sp; if => //; inline *; auto => />; smt(dgtag_ll).
+ by proc; sim.
+ move=> &2 _; proc; sp; if => //; inline *; auto => />; smt(dhtag_ll).
+ move=> &2; proc; sp; if => //; inline *; auto => />; smt(dhtag_ll).
+ by proc; sim.
+ move=> &2 _; proc; inline *; sp; if => //; auto => />; smt(dgtag_ll dhtag_ll).
+ move=> &2; proc; inline *; sp; if => //; auto => />; smt(dgtag_ll dhtag_ll).
+ by proc; sim.
+ by move=> &2 _; proc; inline *; auto.
+ by move=> &2; proc; inline *; auto.
+ by proc; sim.
+ move=> &2 _; proc; sp; if => //; inline *; sp; if => //; auto => />; smt(dgtag_ll dhtag_ll).
+ move=> &2; proc; sp; if => //; inline *; sp; if => //; auto => />; smt(dgtag_ll dhtag_ll).
+ by proc; inline *; auto => /> /#.
+ by move=> &2 _; proc; inline *; auto.
+ by move=> &2; proc; inline *; auto.
by inline *; auto => /> /#.
qed.

(* ------------------------------------------------------------------ *)
(* Step 2a: PlugAndPray.  Record the index of the Dec query that raises  *)
(* the flag, guess it up front, and lose a factor qD.                    *)
(* ------------------------------------------------------------------ *)

local module Ghost = {
  var badIdx : int     (* index (cD) of the Dec query that raised bad *)
  var i      : int     (* the guessed index *)
  var stop   : bool    (* the game has been cut: oracles are inert *)
  var preH   : bool    (* the challenge's sStar was already in logH *)
  var rSet   : bool    (* rStar has been sampled *)
  var rStar  : htag    (* the challenge's r *)
  var gStar  : gtag    (* the challenge's G(r) *)
  var tStar  : htag    (* the challenge's t *)
  var rI     : htag    (* the i-th Dec query's r *)
  var decI   : bool    (* the i-th Dec query evaluated the oracles *)
  var sI     : gtag    (* the i-th Dec query's s *)
  var hI     : htag    (* the i-th Dec query's H(s) *)
  var dI     : bool    (* the i-th Dec query has been answered *)
}.

local module IdealO1 : RawG = {
  include IdealO [fhashG, fhashH, fchallenge, finS, freveal]

  proc init() : unit = {
    IdealO.init();
    Ghost.badIdx <- -1;
  }

  proc fdec(c : gtag * htag) : ptxt option = {
    var s, t, r, g, p, mExt, m, result;
    result <- None;
    if (Mem.cS <> Some c) {
      (s, t) <- fi Mem.sk c;
      r <@ HRO.RO.get(s);
      r <- t - r;
      g <@ GRO.RO.get(r);
      p <- gsub s g;
      mExt <- ext Mem.pk Mem.logH Mem.logG c;
      if (unpad p <> None) {
        m <- oget (unpad p);
        if (!Mem.askH) {
          if (mExt <> Some m) {
            if (!Mem.bad) { Ghost.badIdx <- Exp.WO.cD; }
            Mem.bad <- true;
          }
        }
      } else {
        if (!Mem.askH) {
          if (mExt <> None) {
            if (!Mem.bad) { Ghost.badIdx <- Exp.WO.cD; }
            Mem.bad <- true;
          }
        }
      }
      result <- if Mem.askH then unpad p else mExt;
    }
    return result;
  }
}.

local module G1 = {
  proc main(x : unit) : bool * int = {
    var r;
    r <@ Exp(IdealO1, A).main();
    return (Mem.bad, Ghost.badIdx);
  }
}.

local lemma pr_E0_G1 &m :
  Pr[Exp(IdealO, A).main() @ &m : Mem.bad] = Pr[G1.main() @ &m : res.`1].
proof.
byequiv => //; proc; inline{2} Exp(IdealO1, A).main; wp.
call (: ={glob Mem, glob GRO.RO, glob HRO.RO, glob Exp}).
+ by proc; sim.
+ by proc; sim.
+ by proc; sim.
+ by proc; sim.
+ by proc; inline *; sim.
+ by proc; sim.
by inline *; auto.
qed.

local clone import PlugAndPray as PnP with
  type tval <- int,
  op indices <- range 0 (max 1 qD),
  type tin <- unit,
  type tres <- bool * int
proof *.
realize indices_not_nil. by smt(size_range). qed.

local lemma pr_G1_guess &m :
  Pr[G1.main() @ &m : res.`1]
  <= (max 1 qD)%r * Pr[Guess(G1).main() @ &m : res.`2.`1 /\ res.`1 = res.`2.`2].
proof.
pose phi (_ : glob G1) (o : bool * int) := o.`1 /\ 0 <= o.`2 < max 1 qD.
pose psi (_ : glob G1) (o : bool * int) := o.`2.
have Hpsi : forall g o, phi g o => psi g o \in range 0 (max 1 qD).
+ by move=> g o; rewrite /phi /psi mem_range.
have hcard : size (undup (range 0 (max 1 qD))) = max 1 qD.
+ by rewrite undup_id 1:range_uniq size_range; smt().
have hidx : Pr[G1.main() @ &m : res.`1] = Pr[G1.main() @ &m : phi (glob G1) res].
+ rewrite Pr [mu_split (0 <= res.`2 < max 1 qD)].
  have -> : Pr[G1.main() @ &m : res.`1 /\ !(0 <= res.`2 < max 1 qD)] = 0%r.
  + byphoare => //; hoare; proc; inline Exp(IdealO1, A).main; wp.
    call (: 0 <= Exp.WO.cD /\ (Mem.bad => 0 <= Ghost.badIdx < max 1 qD)).
    + by proc; sp; if => //; inline *; auto => /#.
    + by proc; sp; if => //; inline *; auto => /#.
    + by proc; inline *; sp; if => //; auto => /#.
    + by proc; inline *; auto.
    + by proc; sp; if => //; inline *; wp; sp; if => //; auto => /#.
    + by proc; inline *; auto.
    by inline *; auto => /#.
  by rewrite /phi /=; smt(ge0_mu).
have := PBound_mult G1 phi psi () &m Hpsi.
rewrite hcard -hidx => ->.
apply ler_wpmul2l; 1: smt().
by rewrite Pr [mu_sub] => /#.
qed.

(* The guessed index is sampled up front and bad is computed only at the
   Dec query with that index. *)
local module IdealO3 : RawG = {
  include IdealO [fhashG, fhashH, fchallenge, finS, freveal]

  proc init() : unit = {
    IdealO.init();
    Ghost.i <$ duniform (range 0 (max 1 qD));
  }

  proc fdec(c : gtag * htag) : ptxt option = {
    var s, t, r, g, p, mExt, m, result;
    result <- None;
    if (Mem.cS <> Some c) {
      (s, t) <- fi Mem.sk c;
      r <@ HRO.RO.get(s);
      r <- t - r;
      g <@ GRO.RO.get(r);
      p <- gsub s g;
      mExt <- ext Mem.pk Mem.logH Mem.logG c;
      if (unpad p <> None) {
        m <- oget (unpad p);
        if (!Mem.askH /\ Exp.WO.cD = Ghost.i) {
          if (mExt <> Some m) {
            Mem.bad <- true;
          }
        }
      } else {
        if (!Mem.askH /\ Exp.WO.cD = Ghost.i) {
          if (mExt <> None) {
            Mem.bad <- true;
          }
        }
      }
      result <- if Mem.askH then unpad p else mExt;
    }
    return result;
  }
}.

local lemma pr_guess_E3 &m :
  Pr[Guess(G1).main() @ &m : res.`2.`1 /\ res.`1 = res.`2.`2]
  <= Pr[Exp(IdealO3, A).main() @ &m : Mem.bad].
proof.
byequiv => //; proc; inline{1} G1.main Exp(IdealO1, A).main; wp.
swap{1} 6 -4; wp.
inline{2} Exp(IdealO3, A).WO.init IdealO3.init; swap{2} 5 -4.
seq 2 1 : (i{1} = Ghost.i{2} /\ ={glob A}); 1: by auto.
exists* Ghost.i{2}; elim* => i0.
call (: ={Mem.logG, Mem.logH, Mem.pk, Mem.sk, Mem.cS, Mem.sStar, Mem.challenged, Mem.askH, glob GRO.RO, glob HRO.RO, glob Exp} /\ Ghost.i{2} = i0 /\ (Mem.bad{1} /\ Ghost.badIdx{1} = i0 => Mem.bad{2})).
+ by proc; sp; if => //; inline *; auto => />.
+ by proc; sp; if => //; inline *; auto => />.
+ by proc; inline *; sp; if => //; auto => />.
+ by proc; inline *; auto.
+ proc; sp; if => //; inline *; sp; if => //; auto => /> /#.
+ by proc; inline *; auto.
by inline *; auto => /> /#.
qed.

(* ------------------------------------------------------------------ *)
(* Step 2b: cut the game.  Once H has been queried at sStar (askH), or   *)
(* the challenge's sStar was already in the H log (preH), or the i-th    *)
(* Dec query has been answered, the flag can no longer be raised (in the *)
(* preH case we pay for it), so the oracles may go inert.                *)
(* ------------------------------------------------------------------ *)

local module IdealO3c : RawG = {
  include IdealO [finS, freveal]

  proc init() : unit = {
    IdealO3.init();
    Ghost.stop <- false;
    Ghost.preH <- false;
  }

  proc fhashG(x : htag) : gtag = {
    var y;
    y <- witness;
    if (!Ghost.stop) {
      y <@ GRO.RO.get(x);
      Mem.logG <- (x, y) :: Mem.logG;
    }
    return y;
  }

  proc fhashH(x : gtag) : htag = {
    var y;
    y <- witness;
    if (!Ghost.stop) {
      if (Mem.challenged /\ x = Mem.sStar) {
        Mem.askH <- true;
        Ghost.stop <- true;
      } else {
        y <@ HRO.RO.get(x);
        Mem.logH <- (x, y) :: Mem.logH;
      }
    }
    return y;
  }

  proc fchallenge(m : ptxt) : (gtag * htag) option = {
    var r, s, t, c, result;
    result <- None;
    if (!Ghost.stop) {
      if (Mem.cS = None) {
        r <$ dhtag;
        s <@ GRO.RO.get(r);
        s <- gadd (pad m) s;
        if (s \in map fst Mem.logH) {
          Ghost.preH <- true;
          Ghost.stop <- true;
        } else {
          t <@ HRO.RO.get(s);
          t <- r + t;
          c <- f Mem.pk (s, t);
          Mem.cS <- Some c;
          Mem.sStar <- s;
          Mem.challenged <- true;
          result <- Some c;
        }
      }
    }
    return result;
  }

  proc fdec(c : gtag * htag) : ptxt option = {
    var result;
    result <- None;
    if (!Ghost.stop) {
      result <@ IdealO3.fdec(c);
      if (Exp.WO.cD = Ghost.i) {
        Ghost.stop <- true;
      }
    }
    return result;
  }
}.

local lemma pr_E3_E3c &m :
  Pr[Exp(IdealO3, A).main() @ &m : Mem.bad]
  <= Pr[Exp(IdealO3c, A).main() @ &m : Mem.bad \/ Ghost.preH].
proof.
byequiv (: ={glob A} ==> Mem.bad{1} => Mem.bad{2} \/ Ghost.preH{2}) => //.
proc.
call (: Ghost.stop,
        ={glob Mem, glob GRO.RO, glob HRO.RO, glob Exp, Ghost.i} /\ !Ghost.preH{2},
        Ghost.preH{2} \/
        ((Mem.askH{1} \/ Ghost.i{1} < Exp.WO.cD{1}) /\ (Mem.bad{1} => Mem.bad{2}))).
+ exact A_ll.
(* hashG *)
+ proc; sp; if => //; inline *; sp; rcondt{2} 1; 1: by auto.
  by auto => />.
+ move=> &2 _; proc; sp; if => //; inline *; auto => />; smt(dgtag_ll).
+ move=> &1; proc; sp; if => //; inline *; sp; rcondf 1; 1: by auto.
  by auto.
(* hashH *)
+ proc; sp; if => //; inline *; rcondt{2} 3; 1: by auto.
  case: ((Mem.challenged /\ x = Mem.sStar){2}).
  + rcondt{1} 2; 1: by auto.
    rcondt{2} 3; 1: by auto.
    by auto => />; smt(dhtag_ll).
  rcondf{1} 2; 1: by auto.
  rcondf{2} 3; 1: by auto.
  by auto => />.
+ move=> &2 _; proc; sp; if => //; inline *; auto => />; smt(dhtag_ll).
+ move=> &1; proc; sp; if => //; inline *; sp; rcondf 1; 1: by auto.
  by auto.
(* challenge *)
+ proc; inline *; rcondt{2} 3; 1: by auto.
  sp; if => //; last by auto => />.
  seq 6 6 : (={r0, s, m0} /\ !Ghost.stop{2} /\ !Ghost.preH{2} /\
             ={glob Mem, glob GRO.RO, glob HRO.RO, glob Exp, Ghost.i}); 1: by auto.
  if{2}.
  + by wp; rnd{1}; auto => />; smt(dhtag_ll).
  by auto => />.
+ move=> &2 _; proc; inline *; sp; if => //; auto => />; smt(dgtag_ll dhtag_ll).
+ move=> &1; proc; inline *; sp; rcondf 1; 1: by auto.
  by auto.
(* inS *)
+ proc; inline *; auto => />.
+ by move=> &2 _; proc; inline *; auto.
+ by move=> &1; proc; inline *; auto.
(* dec *)
+ proc; sp; if => //; inline{2} IdealO3c.fdec; sp; rcondt{2} 1; 1: by auto.
  wp; call (: ={glob Mem, glob GRO.RO, glob HRO.RO, glob Exp, Ghost.i}); 1: by sim.
  by auto => /> /#.
+ move=> &2 _; proc; sp; if => //; inline *; sp; if => //; auto => />; smt(dgtag_ll dhtag_ll).
+ move=> &1; proc; sp; if => //; inline *; sp; rcondf 1; 1: by auto.
  by auto.
(* reveal *)
+ by proc; inline *; auto => />.
+ by move=> &2 _; proc; inline *; auto.
+ by move=> &1; proc; inline *; auto.
by inline *; auto => /> /#.
qed.

(* The cost of the cut: sStar was already in the H log at challenge time.
   The G value at the fresh rStar is a fresh uniform gtag unless rStar was
   already in G's table. *)
local lemma pr_E3c_preH &m :
  Pr[Exp(IdealO3c, A).main() @ &m : Ghost.preH]
  <= (qG + qD)%r / cardHtag%r + qH%r / cardGtag%r.
proof.
fel 1 (b2i Mem.challenged + b2i Ghost.preH)
      (fun _ => (qG + qD)%r / cardHtag%r + qH%r / cardGtag%r)
      1 Ghost.preH
      [IdealO3c.fchallenge : (Mem.cS = None /\ !Ghost.stop);
       Exp(IdealO3c, A).WO.dec : false;
       Exp(IdealO3c, A).WO.hashG : false;
       Exp(IdealO3c, A).WO.hashH : false]
      (size Mem.logH <= Exp.WO.cH /\ Exp.WO.cH <= qH /\ Exp.WO.cG <= qG /\
       Exp.WO.cD <= qD /\ 0 <= Exp.WO.cG /\ 0 <= Exp.WO.cD /\
       (!(Mem.challenged \/ Ghost.preH) => fsize GRO.RO.m <= Exp.WO.cG + Exp.WO.cD) /\
       (Mem.challenged => Mem.cS <> None) /\ (Mem.cS = None => !Mem.challenged) /\
       (Ghost.preH => Ghost.stop) /\ (Ghost.preH => !Mem.challenged)).
+ by rewrite range_ltn // range_geq // BRA.big_cons BRA.big_nil /predT /=; smt().
+ by move=> &hr /#.
+ by inline *; auto => />; smt(fsize_empty).
(* dec *)
+ by exfalso.
+ by move=> c; exfalso.
+ move=> b c; proc; sp; if => //; inline *; sp; if; last by auto => /> /#.
  by sp; if; [by auto => />; smt(fsize_set) | by auto => /> /#].
(* hashG *)
+ by exfalso.
+ by move=> c; exfalso.
+ move=> b c; proc; sp; if => //; inline *; sp; if; last by auto => /> /#.
  by auto => />; smt(fsize_set).
(* hashH *)
+ by exfalso.
+ by move=> c; exfalso.
+ move=> b c; proc; sp; if => //; inline *; sp; if; last by auto => /> /#.
  by if; [by auto => /> /# | by auto => /> /#].
(* challenge *)
+ proc; sp; rcondt 1; 1: by auto.
  rcondt 1; 1: by auto.
  inline *.
  seq 2 : (x \in GRO.RO.m) ((qG + qD)%r / cardHtag%r) 1%r 1%r (qH%r / cardGtag%r)
          (!Ghost.preH /\ !Mem.challenged /\ size Mem.logH <= qH /\ fsize GRO.RO.m <= qG + qD).
  + by auto => /> /#.
  + wp; rnd; skip => /> &hr _ _ _ hsz.
    have := mu_dhtag_fdom GRO.RO.m{hr}.
    by smt(cardHtag_gt0).
  + by pr_bounded.
  + by pr_bounded.
  + rcondt 2; 1: by auto.
    seq 4 : (s \in unzip1 Mem.logH) (qH%r / cardGtag%r) 1%r _ 0%r (!Ghost.preH) => //.
    + by auto.
    + wp; rnd; skip => /> &hr hpre hch hsz _ hx.
      have -> : (fun (r1 : gtag) => gadd (pad m{hr}) (oget GRO.RO.m{hr}.[x{hr} <- r1].[x{hr}]) \in unzip1 Mem.logH{hr})
                = (fun g => gadd (pad m{hr}) g \in unzip1 Mem.logH{hr}).
      + by apply fun_ext => g; rewrite get_set_sameE.
      have := mu_dgtag_mem_shift (pad m{hr}) (unzip1 Mem.logH{hr}).
      by rewrite size_map; smt(cardGtag_gt0).
    by hoare; rcondf 1; [by auto | by auto].
  by smt().
+ move=> c; proc; sp; rcondt 1; 1: by auto.
  rcondt 1; 1: by auto.
  inline *; seq 6 : (c = 0 /\ !Mem.challenged /\ !Ghost.preH /\ size Mem.logH <= Exp.WO.cH /\
                    Exp.WO.cH <= qH /\ Exp.WO.cG <= qG /\ Exp.WO.cD <= qD /\
                    0 <= Exp.WO.cG /\ 0 <= Exp.WO.cD).
  + by auto => /> /#.
  by if; auto => /> /#.
move=> b c; proc; sp; if; last by auto.
rcondf 1; 1: by auto => /#.
by auto.
qed.

(* ------------------------------------------------------------------ *)
(* Step 2c: lazy/eager.  In the cut game the Dec queries other than the *)
(* i-th one only feed the (unused) real decryption, so their oracle      *)
(* evaluations are `sample`s, and PROM's RO_LRO_D lets us drop them.     *)
(* First G (Dec(j <> i): h <@ H.get(s); G.sample(t - h)).                *)
(* ------------------------------------------------------------------ *)

local module F3a (G : GRO.RO) = {
  module O : RawG = {
    proc init() : unit = {
      (Mem.pk, Mem.sk) <$ dkeys;
      G.init();
      HRO.RO.init();
      Mem.logG <- [];
      Mem.logH <- [];
      Mem.cS   <- None;
      Mem.sStar <- gzero;
      Mem.challenged <- false;
      Mem.askH <- false;
      Mem.bad  <- false;
      Ghost.badIdx <- -1;
      Ghost.i <$ duniform (range 0 (max 1 qD));
      Ghost.stop <- false;
      Ghost.preH <- false;
    }

    proc fhashG(x : htag) : gtag = {
      var y;
      y <- witness;
      if (!Ghost.stop) {
        y <@ G.get(x);
        Mem.logG <- (x, y) :: Mem.logG;
      }
      return y;
    }

    proc fhashH = IdealO3c.fhashH
    proc finS   = IdealO.finS
    proc freveal = IdealO.freveal

    proc fchallenge(m : ptxt) : (gtag * htag) option = {
      var r, s, t, c, result;
      result <- None;
      if (!Ghost.stop) {
        if (Mem.cS = None) {
          r <$ dhtag;
          s <@ G.get(r);
          s <- gadd (pad m) s;
          if (s \in map fst Mem.logH) {
            Ghost.preH <- true;
            Ghost.stop <- true;
          } else {
            t <@ HRO.RO.get(s);
            t <- r + t;
            c <- f Mem.pk (s, t);
            Mem.cS <- Some c;
            Mem.sStar <- s;
            Mem.challenged <- true;
            result <- Some c;
          }
        }
      }
      return result;
    }

    proc fdec(c : gtag * htag) : ptxt option = {
      var s, t, r, g, p, mExt, m, result;
      result <- None;
      if (!Ghost.stop) {
        if (Exp.WO.cD = Ghost.i) {
          if (Mem.cS <> Some c) {
            (s, t) <- fi Mem.sk c;
            r <@ HRO.RO.get(s);
            r <- t - r;
            g <@ G.get(r);
            p <- gsub s g;
            mExt <- ext Mem.pk Mem.logH Mem.logG c;
            if (unpad p <> None) {
              m <- oget (unpad p);
              if (mExt <> Some m) {
                Mem.bad <- true;
              }
            } else {
              if (mExt <> None) {
                Mem.bad <- true;
              }
            }
            result <- mExt;
          }
          Ghost.stop <- true;
        } else {
          if (Mem.cS <> Some c) {
            (s, t) <- fi Mem.sk c;
            r <@ HRO.RO.get(s);
            G.sample(t - r);
            result <- ext Mem.pk Mem.logH Mem.logG c;
          }
        }
      }
      return result;
    }
  }

  proc distinguish(x : unit) : bool = {
    var r;
    r <@ Exp(O, A).main();
    return Mem.bad;
  }
}.

local lemma pr_E3c_F3a &m :
  Pr[Exp(IdealO3c, A).main() @ &m : Mem.bad] = Pr[F3a(GRO.RO).distinguish() @ &m : res].
proof.
byequiv => //; proc; inline{2} Exp(F3a(GRO.RO).O, A).main; wp.
call (: ={glob Mem, glob GRO.RO, glob HRO.RO, glob Exp, Ghost.i, Ghost.preH, Ghost.stop} /\
        (Mem.askH{1} => Ghost.stop{1})).
+ by proc; sp; if => //; inline *; sp; if => //; auto => />.
+ proc; sp; if => //; inline *; sp; if => //; last by auto => />.
  by if => //; auto => /> /#.
+ proc; inline *; sp; if => //; last by auto => />.
  sp; if => //; last by auto => />.
  seq 6 6 : (={r0, x, s, m0, result, glob Mem, glob GRO.RO, glob HRO.RO, glob Exp, Ghost.i, Ghost.preH, Ghost.stop} /\
             (Mem.askH{1} => Ghost.stop{1})); 1: by auto => />.
  by if => //; auto => /> /#.
+ by proc; inline *; auto.
+ proc; sp; if => //; inline{1} IdealO3c.fdec; inline{2} F3a(GRO.RO).O.fdec.
  sp; if => //; last by auto => />.
  case: (Exp.WO.cD{2} = Ghost.i{2}).
  + rcondt{2} 1; 1: by auto.
    inline{1} IdealO3.fdec; sp; if; first by auto => /> /#.
    + by inline *; auto => /> /#.
    by auto => /> /#.
  rcondf{2} 1; 1: by auto.
  inline{1} IdealO3.fdec; sp; if; first by auto => /> /#.
  + by inline *; auto => /> /#.
  by auto => /> /#.
+ by proc; inline *; auto.
by inline *; auto => /> /#.
qed.

local lemma pr_F3a_LRO &m :
  Pr[F3a(GRO.RO).distinguish() @ &m : res] = Pr[F3a(GRO.LRO).distinguish() @ &m : res].
proof.
byequiv (GRO.FullEager.RO_LRO_D F3a _) => //.
by move=> _; exact dgtag_ll.
qed.

(* Then H (Dec(j <> i): H.sample(s)); G is now lazy (GRO.LRO). *)
local module F3b (H : HRO.RO) = {
  module O : RawG = {
    proc init() : unit = {
      (Mem.pk, Mem.sk) <$ dkeys;
      GRO.LRO.init();
      H.init();
      Mem.logG <- [];
      Mem.logH <- [];
      Mem.cS   <- None;
      Mem.sStar <- gzero;
      Mem.challenged <- false;
      Mem.askH <- false;
      Mem.bad  <- false;
      Ghost.badIdx <- -1;
      Ghost.i <$ duniform (range 0 (max 1 qD));
      Ghost.stop <- false;
      Ghost.preH <- false;
    }

    proc fhashG(x : htag) : gtag = {
      var y;
      y <- witness;
      if (!Ghost.stop) {
        y <@ GRO.LRO.get(x);
        Mem.logG <- (x, y) :: Mem.logG;
      }
      return y;
    }

    proc fhashH(x : gtag) : htag = {
      var y;
      y <- witness;
      if (!Ghost.stop) {
        if (Mem.challenged /\ x = Mem.sStar) {
          Mem.askH <- true;
          Ghost.stop <- true;
        } else {
          y <@ H.get(x);
          Mem.logH <- (x, y) :: Mem.logH;
        }
      }
      return y;
    }

    proc finS   = IdealO.finS
    proc freveal = IdealO.freveal

    proc fchallenge(m : ptxt) : (gtag * htag) option = {
      var r, s, t, c, result;
      result <- None;
      if (!Ghost.stop) {
        if (Mem.cS = None) {
          r <$ dhtag;
          s <@ GRO.LRO.get(r);
          s <- gadd (pad m) s;
          if (s \in map fst Mem.logH) {
            Ghost.preH <- true;
            Ghost.stop <- true;
          } else {
            t <@ H.get(s);
            t <- r + t;
            c <- f Mem.pk (s, t);
            Mem.cS <- Some c;
            Mem.sStar <- s;
            Mem.challenged <- true;
            result <- Some c;
          }
        }
      }
      return result;
    }

    proc fdec(c : gtag * htag) : ptxt option = {
      var s, t, r, g, p, mExt, m, result;
      result <- None;
      if (!Ghost.stop) {
        if (Exp.WO.cD = Ghost.i) {
          if (Mem.cS <> Some c) {
            (s, t) <- fi Mem.sk c;
            r <@ H.get(s);
            r <- t - r;
            g <@ GRO.LRO.get(r);
            p <- gsub s g;
            mExt <- ext Mem.pk Mem.logH Mem.logG c;
            if (unpad p <> None) {
              m <- oget (unpad p);
              if (mExt <> Some m) {
                Mem.bad <- true;
              }
            } else {
              if (mExt <> None) {
                Mem.bad <- true;
              }
            }
            result <- mExt;
          }
          Ghost.stop <- true;
        } else {
          if (Mem.cS <> Some c) {
            (s, t) <- fi Mem.sk c;
            H.sample(s);
            result <- ext Mem.pk Mem.logH Mem.logG c;
          }
        }
      }
      return result;
    }
  }

  proc distinguish(x : unit) : bool = {
    var r;
    r <@ Exp(O, A).main();
    return Mem.bad;
  }
}.

local lemma pr_F3a_F3b &m :
  Pr[F3a(GRO.LRO).distinguish() @ &m : res] = Pr[F3b(HRO.RO).distinguish() @ &m : res].
proof.
byequiv => //; proc; inline{1} Exp(F3a(GRO.LRO).O, A).main; inline{2} Exp(F3b(HRO.RO).O, A).main; wp.
call (: ={glob Mem, glob GRO.RO, glob HRO.RO, glob Exp, Ghost.badIdx, Ghost.i, Ghost.preH, Ghost.stop}).
+ by proc; sp; if => //; inline *; sp; if => //; auto => />.
+ proc; sp; if => //; inline *; sp; if => //; last by auto => />.
  by if => //; auto => />.
+ proc; inline *; sp; if => //; last by auto => />.
  sp; if => //; last by auto => />.
  seq 6 6 : (={r0, x, s, m0, result, glob Mem, glob GRO.RO, glob HRO.RO, glob Exp, Ghost.badIdx, Ghost.i, Ghost.preH, Ghost.stop}); 1: by auto => />.
  by if => //; auto => />.
+ by proc; inline *; auto.
+ proc; sp; if => //; inline{1} F3a(GRO.LRO).O.fdec; inline{2} F3b(HRO.RO).O.fdec.
  sp; if => //; last by auto => />.
  if => //.
  + sp; if => //; last by auto => />.
    by inline *; auto => />.
  sp; if => //; last by auto => />.
  by inline *; auto => />.
+ by proc; inline *; auto.
by inline *; auto => />.
qed.

local lemma pr_F3b_LRO &m :
  Pr[F3b(HRO.RO).distinguish() @ &m : res] = Pr[F3b(HRO.LRO).distinguish() @ &m : res].
proof.
byequiv (HRO.FullEager.RO_LRO_D F3b _) => //.
by move=> _; exact dhtag_ll.
qed.

(* ------------------------------------------------------------------ *)
(* Step 2d: the challenge's G value is a fresh sample that is NOT       *)
(* stored (up to bad: G queried at rStar, or the i-th Dec query's r     *)
(* equals rStar).  Both oracles are now lazy (LRO).                     *)
(* ------------------------------------------------------------------ *)

local module O4 : RawG = {
  proc init() : unit = {
    (Mem.pk, Mem.sk) <$ dkeys;
    GRO.LRO.init();
    HRO.LRO.init();
    Mem.logG <- [];
    Mem.logH <- [];
    Mem.cS   <- None;
    Mem.sStar <- gzero;
    Mem.challenged <- false;
    Mem.askH <- false;
    Mem.bad  <- false;
    Ghost.badIdx <- -1;
    Ghost.i <$ duniform (range 0 (max 1 qD));
    Ghost.stop <- false;
    Ghost.preH <- false;
    Ghost.decI <- false;
    Ghost.rSet <- false;
  }

  proc fhashG = F3b(HRO.LRO).O.fhashG
  proc fhashH = F3b(HRO.LRO).O.fhashH
  proc finS   = IdealO.finS
  proc freveal = IdealO.freveal

  proc fchallenge(m : ptxt) : (gtag * htag) option = {
    var r, s, t, c, g, result;
    result <- None;
    if (!Ghost.stop) {
      if (Mem.cS = None) {
        r <$ dhtag;
        if (!Ghost.rSet) {
          Ghost.rStar <- r;
          Ghost.rSet <- true;
        }
        g <$ dgtag;
        Ghost.gStar <- g;
        s <- gadd (pad m) Ghost.gStar;
        if (s \in map fst Mem.logH) {
          Ghost.preH <- true;
          Ghost.stop <- true;
        } else {
          t <@ HRO.LRO.get(s);
          t <- r + t;
          Ghost.tStar <- t;
          c <- f Mem.pk (s, t);
          Mem.cS <- Some c;
          Mem.sStar <- s;
          Mem.challenged <- true;
          result <- Some c;
        }
      }
    }
    return result;
  }

  proc fdec(c : gtag * htag) : ptxt option = {
    var s, t, r, g, p, mExt, m, result;
    result <- None;
    if (!Ghost.stop) {
      if (Exp.WO.cD = Ghost.i) {
        if (Mem.cS <> Some c) {
          (s, t) <- fi Mem.sk c;
          r <@ HRO.LRO.get(s);
          r <- t - r;
          if (!Ghost.decI) {
            Ghost.rI <- r;
            Ghost.decI <- true;
          }
          g <@ GRO.LRO.get(r);
          p <- gsub s g;
          mExt <- ext Mem.pk Mem.logH Mem.logG c;
          if (unpad p <> None) {
            m <- oget (unpad p);
            if (mExt <> Some m) {
              Mem.bad <- true;
            }
          } else {
            if (mExt <> None) {
              Mem.bad <- true;
            }
          }
          result <- mExt;
        }
        Ghost.stop <- true;
      } else {
        if (Mem.cS <> Some c) {
          result <- ext Mem.pk Mem.logH Mem.logG c;
        }
      }
    }
    return result;
  }
}.

(* the divergence event of the hop, on O4's memory *)
op badG (rSet : bool) (rStar : htag) (logG : (htag * gtag) list) (decI : bool) (rI : htag) : bool =
  rSet /\ (rStar \in unzip1 logG \/ (decI /\ rI = rStar)).

local lemma pr_E3L_O4 &m :
  Pr[F3b(HRO.LRO).distinguish() @ &m : res]
  <= Pr[Exp(O4, A).main() @ &m : Mem.bad \/ badG Ghost.rSet Ghost.rStar Mem.logG Ghost.decI Ghost.rI].
proof.
byequiv (: ={glob A} ==> res{1} => Mem.bad{2} \/ badG Ghost.rSet{2} Ghost.rStar{2} Mem.logG{2} Ghost.decI{2} Ghost.rI{2}) => //.
proc; inline{1} Exp(F3b(HRO.LRO).O, A).main; wp.
call (: badG Ghost.rSet Ghost.rStar Mem.logG Ghost.decI Ghost.rI,
        ={glob Mem, glob HRO.RO, glob Exp, Ghost.i, Ghost.preH, Ghost.stop} /\
        (Mem.askH{2} => Ghost.stop{2}) /\ (Ghost.decI{2} => Ghost.stop{2}) /\
        (Mem.challenged{2} => Ghost.rSet{2}) /\ (Mem.challenged{2} => Mem.cS{2} <> None) /\
        (Ghost.rSet{2} => Mem.cS{2} <> None \/ Ghost.stop{2}) /\
        (!Mem.challenged{2} => !Ghost.stop{2} => ={GRO.RO.m} /\
           (forall x, x \in GRO.RO.m{2} => x \in unzip1 Mem.logG{2})) /\
        (Mem.challenged{2} => GRO.RO.m{1} = GRO.RO.m{2}.[Ghost.rStar{2} <- Ghost.gStar{2}] /\
           Ghost.rStar{2} \notin GRO.RO.m{2})).
+ exact A_ll.
(* hashG *)
+ proc; sp; if => //; inline *; sp; if => //; last by auto => />.
  by auto => />; smt(mem_set get_setE set_set_neqE).
+ by move=> &2 _; islossless.
+ move=> _; conseq (: _ ==> true) (: badG Ghost.rSet Ghost.rStar Mem.logG Ghost.decI Ghost.rI
                                   ==> badG Ghost.rSet Ghost.rStar Mem.logG Ghost.decI Ghost.rI) => //.
  + by proc; sp; if => //; inline *; sp; if => //; auto => />; smt().
  by islossless.
(* hashH *)
+ proc; sp; if => //; inline *; sp; if => //; last by auto => />.
  by if => //; auto => /> /#.
+ by move=> &2 _; islossless.
+ move=> _; conseq (: _ ==> true) (: badG Ghost.rSet Ghost.rStar Mem.logG Ghost.decI Ghost.rI
                                   ==> badG Ghost.rSet Ghost.rStar Mem.logG Ghost.decI Ghost.rI) => //.
  + by proc; sp; if => //; inline *; sp; if => //; [if => //; auto => /> | auto].
  by islossless.
(* challenge *)
+ proc; inline{1} F3b(HRO.LRO).O.fchallenge; inline{2} O4.fchallenge.
  sp; if => //; last by auto => />.
  sp; if => //; last by auto => />.
  rcondt{2} 2; 1: by auto => /#.
  seq 3 6 : (={m0, result, glob Mem, glob HRO.RO, glob Exp, Ghost.i, Ghost.preH, Ghost.stop} /\
             r0{1} = r0{2} /\ Ghost.rSet{2} /\ Ghost.rStar{2} = r0{2} /\
             !Mem.challenged{2} /\ !Ghost.stop{2} /\ !Ghost.decI{2} /\ !Mem.askH{2} /\
             (r0{2} \in unzip1 Mem.logG{2} \/
              (s{1} = s{2} /\ GRO.RO.m{1} = GRO.RO.m{2}.[r0{2} <- Ghost.gStar{2}] /\
               r0{2} \notin GRO.RO.m{2}))).
  + by inline *; auto => />; smt(get_set_sameE mem_set).
  case: (r0{2} \in unzip1 Mem.logG{2}).
  + conseq (: _ ==> Ghost.rSet{2} /\ Ghost.rStar{2} \in unzip1 Mem.logG{2}).
    + by rewrite /badG; smt().
    by if{1}; if{2}; inline *; auto => />; smt(dhtag_ll).
  if => //.
  + by smt().
  + by auto => /> /#.
  by inline *; auto => />; rewrite /badG /=; smt().
+ by move=> &2 _; islossless.
+ move=> _; conseq (: _ ==> true) (: badG Ghost.rSet Ghost.rStar Mem.logG Ghost.decI Ghost.rI
                                   ==> badG Ghost.rSet Ghost.rStar Mem.logG Ghost.decI Ghost.rI) => //.
  + proc; inline *; sp; if => //; last by auto.
    sp; if => //; last by auto.
    seq 5 : (badG Ghost.rSet Ghost.rStar Mem.logG Ghost.decI Ghost.rI); 1: by auto => /> /#.
    by if; auto => /> /#.
  by islossless.
(* inS *)
+ by proc; inline *; auto.
+ by move=> &2 _; islossless.
+ by move=> _; proc; inline *; auto.
(* dec *)
+ proc; sp; if => //; inline{1} F3b(HRO.LRO).O.fdec; inline{2} O4.fdec.
  sp; if => //; last by auto => />.
  if => //.
  + sp; if => //; last by auto => /> /#.
    by inline *; auto => />; smt(mem_set get_setE set_set_neqE).
  if => //; last by auto => />.
  by inline *; auto => /> /#.
+ by move=> &2 _; islossless.
+ move=> _; conseq (: _ ==> true) (: badG Ghost.rSet Ghost.rStar Mem.logG Ghost.decI Ghost.rI
                                   ==> badG Ghost.rSet Ghost.rStar Mem.logG Ghost.decI Ghost.rI) => //.
  + proc; sp; if => //; inline *; sp; if => //; last by auto.
    if => //; last by if => //; auto => /> /#.
    by if => //; auto => /> /#.
  by islossless.
(* reveal *)
+ by proc; inline *; auto.
+ by move=> &2 _; islossless.
+ by move=> _; proc; inline *; auto.
by inline *; auto => /> /#.
qed.

(* ------------------------------------------------------------------ *)
(* Step 2e: defer the challenge's H value.  First move the sampling of  *)
(* rStar after the evaluation of H(sStar) (O4b); then replace           *)
(* (rStar, hStar) by (tStar, hStar) with tStar fresh and rStar := tStar  *)
(* - hStar recomputed at the end (F4); the challenge's H evaluation is   *)
(* then a `sample`, and RO_LRO_D drops it.                               *)
(* ------------------------------------------------------------------ *)

local module O4b : RawG = {
  include O4 [init, fhashG, fhashH, finS, freveal, fdec]

  proc fchallenge(m : ptxt) : (gtag * htag) option = {
    var r, s, t, c, g, result;
    result <- None;
    if (!Ghost.stop) {
      if (Mem.cS = None) {
        g <$ dgtag;
        Ghost.gStar <- g;
        s <- gadd (pad m) Ghost.gStar;
        if (s \in map fst Mem.logH) {
          r <$ dhtag;
          if (!Ghost.rSet) {
            Ghost.rStar <- r;
            Ghost.rSet <- true;
          }
          Ghost.preH <- true;
          Ghost.stop <- true;
        } else {
          t <@ HRO.LRO.get(s);
          r <$ dhtag;
          if (!Ghost.rSet) {
            Ghost.rStar <- r;
            Ghost.rSet <- true;
          }
          t <- r + t;
          Ghost.tStar <- t;
          c <- f Mem.pk (s, t);
          Mem.cS <- Some c;
          Mem.sStar <- s;
          Mem.challenged <- true;
          result <- Some c;
        }
      }
    }
    return result;
  }
}.

local lemma pr_O4_O4b &m :
  Pr[Exp(O4, A).main() @ &m : Mem.bad \/ badG Ghost.rSet Ghost.rStar Mem.logG Ghost.decI Ghost.rI]
  = Pr[Exp(O4b, A).main() @ &m : Mem.bad \/ badG Ghost.rSet Ghost.rStar Mem.logG Ghost.decI Ghost.rI].
proof.
byequiv => //; proc.
call (: ={glob Mem, glob GRO.RO, glob HRO.RO, glob Exp, Ghost.badIdx, Ghost.i, Ghost.preH, Ghost.stop, Ghost.rSet, Ghost.decI, Ghost.rI, Ghost.rStar}).
+ by proc; sim.
+ by proc; sim.
+ proc; inline{1} O4.fchallenge; inline{2} O4b.fchallenge.
  sp; if => //; last by auto.
  sp; if => //; last by auto.
  swap{1} [1..2] 3.
  seq 3 3 : (={g, s, m0, result, glob Mem, glob GRO.RO, glob HRO.RO, glob Exp, Ghost.badIdx, Ghost.i, Ghost.preH, Ghost.stop, Ghost.rSet, Ghost.decI, Ghost.rI, Ghost.rStar}); 1: by auto.
  if{2}.
  + rcondt{1} 3; 1: by auto.
    by auto.
  rcondf{1} 3; 1: by auto.
  inline *; swap{1} [1..2] 4.
  by auto.
+ by proc; sim.
+ by proc; sim.
+ by proc; sim.
by inline *; auto.
qed.

local module F4 (H : HRO.RO) = {
  module O : RawG = {
    proc init() : unit = {
      (Mem.pk, Mem.sk) <$ dkeys;
      GRO.LRO.init();
      H.init();
      Mem.logG <- [];
      Mem.logH <- [];
      Mem.cS   <- None;
      Mem.sStar <- gzero;
      Mem.challenged <- false;
      Mem.askH <- false;
      Mem.bad  <- false;
      Ghost.badIdx <- -1;
      Ghost.i <$ duniform (range 0 (max 1 qD));
      Ghost.stop <- false;
      Ghost.preH <- false;
      Ghost.decI <- false;
      Ghost.rSet <- false;
      Ghost.dI <- false;
    }

    proc fhashG(x : htag) : gtag = {
      var y;
      y <- witness;
      if (!Ghost.stop) {
        y <@ GRO.LRO.get(x);
        Mem.logG <- (x, y) :: Mem.logG;
      }
      return y;
    }

    proc fhashH(x : gtag) : htag = {
      var y;
      y <- witness;
      if (!Ghost.stop) {
        if (Mem.challenged /\ x = Mem.sStar) {
          Mem.askH <- true;
          Ghost.stop <- true;
        } else {
          y <@ H.get(x);
          Mem.logH <- (x, y) :: Mem.logH;
        }
      }
      return y;
    }

    proc finS   = IdealO.finS
    proc freveal = IdealO.freveal

    proc fchallenge(m : ptxt) : (gtag * htag) option = {
      var r, s, t, c, g, result;
      result <- None;
      if (!Ghost.stop) {
        if (Mem.cS = None) {
          g <$ dgtag;
          Ghost.gStar <- g;
          s <- gadd (pad m) Ghost.gStar;
          if (s \in map fst Mem.logH) {
            r <$ dhtag;
            if (!Ghost.rSet) {
              Ghost.rStar <- r;
              Ghost.rSet <- true;
            }
            Ghost.preH <- true;
            Ghost.stop <- true;
          } else {
            H.sample(s);
            t <$ dhtag;
            Ghost.rSet <- true;
            Ghost.tStar <- t;
            c <- f Mem.pk (s, t);
            Mem.cS <- Some c;
            Mem.sStar <- s;
            Mem.challenged <- true;
            result <- Some c;
          }
        }
      }
      return result;
    }

    proc fdec(c : gtag * htag) : ptxt option = {
      var s, t, r, g, p, mExt, m, result;
      result <- None;
      if (!Ghost.stop) {
        if (Exp.WO.cD = Ghost.i) {
          if (Mem.cS <> Some c) {
            (s, t) <- fi Mem.sk c;
            r <@ H.get(s);
            if (!Ghost.decI) {
              Ghost.sI <- s;
              Ghost.hI <- r;
            }
            r <- t - r;
            if (!Ghost.decI) {
              Ghost.rI <- r;
              Ghost.decI <- true;
            }
            g <@ GRO.LRO.get(r);
            p <- gsub s g;
            mExt <- ext Mem.pk Mem.logH Mem.logG c;
            if (unpad p <> None) {
              m <- oget (unpad p);
              if (mExt <> Some m) {
                Mem.bad <- true;
              }
            } else {
              if (mExt <> None) {
                Mem.bad <- true;
              }
            }
            result <- mExt;
          }
          Ghost.stop <- true;
          Ghost.dI <- true;
        } else {
          if (Mem.cS <> Some c) {
            result <- ext Mem.pk Mem.logH Mem.logG c;
          }
        }
      }
      return result;
    }
  }

  proc distinguish(x : unit) : bool = {
    var r, h;
    r <@ Exp(O, A).main();
    if (Mem.challenged) {
      h <@ H.get(Mem.sStar);
      Ghost.rStar <- Ghost.tStar - h;
    }
    return Mem.bad \/ badG Ghost.rSet Ghost.rStar Mem.logG Ghost.decI Ghost.rI;
  }
}.

local lemma pr_O4b_F4 &m :
  Pr[Exp(O4b, A).main() @ &m : Mem.bad \/ badG Ghost.rSet Ghost.rStar Mem.logG Ghost.decI Ghost.rI]
  = Pr[F4(HRO.RO).distinguish() @ &m : res].
proof.
byequiv => //; proc; inline{2} Exp(F4(HRO.RO).O, A).main; wp.
seq 2 2 : (={glob Mem, glob GRO.RO, glob HRO.RO, glob Exp, Ghost.i, Ghost.preH, Ghost.stop,
              Ghost.rSet, Ghost.rI, Ghost.decI} /\
           (Mem.askH{2} => Ghost.stop{2}) /\ (Ghost.decI{2} => Ghost.stop{2}) /\
           (Mem.challenged{2} => Ghost.rSet{2}) /\ (Mem.challenged{2} => Mem.cS{2} <> None) /\
           (Ghost.rSet{2} => Mem.cS{2} <> None \/ Ghost.stop{2}) /\
           (Mem.challenged{2} => Mem.sStar{2} \in HRO.RO.m{2} /\
              Ghost.rStar{1} = Ghost.tStar{2} - oget HRO.RO.m{2}.[Mem.sStar{2}]) /\
           (Ghost.rSet{2} => !Mem.challenged{2} => Ghost.rStar{1} = Ghost.rStar{2})).
+ call (: (={glob Mem, glob GRO.RO, glob HRO.RO, glob Exp, Ghost.i, Ghost.preH, Ghost.stop,
              Ghost.rSet, Ghost.rI, Ghost.decI} /\
           (Mem.askH{2} => Ghost.stop{2}) /\ (Ghost.decI{2} => Ghost.stop{2}) /\
           (Mem.challenged{2} => Ghost.rSet{2}) /\ (Mem.challenged{2} => Mem.cS{2} <> None) /\
           (Ghost.rSet{2} => Mem.cS{2} <> None \/ Ghost.stop{2}) /\
           (Mem.challenged{2} => Mem.sStar{2} \in HRO.RO.m{2} /\
              Ghost.rStar{1} = Ghost.tStar{2} - oget HRO.RO.m{2}.[Mem.sStar{2}]) /\
           (Ghost.rSet{2} => !Mem.challenged{2} => Ghost.rStar{1} = Ghost.rStar{2}))).
  + by proc; sp; if => //; inline *; sp; if => //; [by auto => /> /# | by auto => />].
  + proc; sp; if => //; inline *; sp; if => //; last by auto => />.
    by if => //; [by auto => /> /# | by auto => />; smt(get_setE mem_set)].
  + proc; inline{1} O4b.fchallenge; inline{2} F4(HRO.RO).O.fchallenge.
    sp; if => //; last by auto => />.
    sp; if => //; last by auto => />.
    seq 3 3 : (={g, s, m0, result} /\ (={glob Mem, glob GRO.RO, glob HRO.RO, glob Exp, Ghost.i, Ghost.preH, Ghost.stop,
              Ghost.rSet, Ghost.rI, Ghost.decI} /\
           (Mem.askH{2} => Ghost.stop{2}) /\ (Ghost.decI{2} => Ghost.stop{2}) /\
           (Mem.challenged{2} => Ghost.rSet{2}) /\ (Mem.challenged{2} => Mem.cS{2} <> None) /\
           (Ghost.rSet{2} => Mem.cS{2} <> None \/ Ghost.stop{2}) /\
           (Mem.challenged{2} => Mem.sStar{2} \in HRO.RO.m{2} /\
              Ghost.rStar{1} = Ghost.tStar{2} - oget HRO.RO.m{2}.[Mem.sStar{2}]) /\
           (Ghost.rSet{2} => !Mem.challenged{2} => Ghost.rStar{1} = Ghost.rStar{2})) /\
               !Mem.challenged{2} /\ !Ghost.stop{2} /\ Mem.cS{2} = None /\ !Ghost.rSet{2}).
    + by auto => /> /#.
    if => //; first by auto => /> /#.
    inline *.
    seq 4 4 : (={g, s, m0, result, x, glob Mem, glob GRO.RO, glob HRO.RO, glob Exp, Ghost.i,
                Ghost.preH, Ghost.stop, Ghost.rSet, Ghost.rI, Ghost.decI} /\
               !Mem.challenged{2} /\ !Ghost.stop{2} /\ Mem.cS{2} = None /\ !Ghost.rSet{2} /\
               (Ghost.decI{2} => Ghost.stop{2}) /\ (Mem.askH{2} => Ghost.stop{2}) /\
               x{1} = s{1} /\ s{1} \in HRO.RO.m{1} /\ t{1} = oget HRO.RO.m{1}.[s{1}]).
    + by auto => />; smt(get_set_sameE mem_set).
    rcondt{1} 2; 1: by auto => /#.
    wp; rnd (fun r0 => r0 + t{1}) (fun t' => t' - t{1}).
    by auto => />; smt(HTag.addrK HTag.subrK FinHtag.dunifin1E FinHtag.dunifin_fu).
  + by proc; inline *; auto.
  + proc; sp; if => //; inline{1} O4b.fdec; inline{2} F4(HRO.RO).O.fdec.
    sp; if => //; last by auto => />.
    if => //; last by if => //; auto => />.
    if => //; last by auto => /> /#.
    by inline *; auto => />; smt(get_setE mem_set).
  + by proc; inline *; auto.
  by inline *; auto => /> /#.
sp 0 1; if{2}.
+ by inline *; auto => />; smt(dhtag_ll).
by auto => /> /#.
qed.

local lemma pr_F4_LRO &m :
  Pr[F4(HRO.RO).distinguish() @ &m : res] = Pr[F4(HRO.LRO).distinguish() @ &m : res].
proof.
byequiv (HRO.FullEager.RO_LRO_D F4 _) => //.
by move=> _; exact dhtag_ll.
qed.

(* ------------------------------------------------------------------ *)
(* Step 2f: the final game E5 = F4(HRO.LRO).  Its state invariant.      *)
(* ------------------------------------------------------------------ *)

local module E5 = F4(HRO.LRO).

local lemma inv_hashG :
  hoare[Exp(E5.O, A).WO.hashG : (Mem.pk, Mem.sk) \in dkeys /\ 0 <= Exp.WO.cD /\ 0 <= Exp.WO.cH /\
  size Mem.logG <= Exp.WO.cG /\ Exp.WO.cG <= qG /\
  logs_okH Mem.logH HRO.RO.m /\ logs_okG Mem.logG GRO.RO.m /\
  (!Ghost.stop => forall x, x \in GRO.RO.m => x \in unzip1 Mem.logG) /\
  (!Ghost.stop => forall x, x \in HRO.RO.m => x \in unzip1 Mem.logH) /\
  (Mem.askH => Ghost.stop) /\ (Ghost.decI => Ghost.stop) /\ (Ghost.dI => Ghost.stop) /\
  (Mem.challenged => Ghost.rSet) /\ (Ghost.rSet => Mem.cS <> None \/ Ghost.stop) /\
  (Mem.cS <> None => Mem.challenged) /\
  (Mem.challenged => Mem.cS = Some (f Mem.pk (Mem.sStar, Ghost.tStar))) /\
  (Mem.challenged => !(Mem.sStar \in unzip1 Mem.logH)) /\
  (Mem.challenged => Mem.sStar \in HRO.RO.m => Ghost.decI /\ Ghost.sI = Mem.sStar) /\
  (Ghost.rSet => !Mem.challenged => !Ghost.decI) /\
  (Ghost.decI => Mem.challenged => Ghost.sI = Mem.sStar => Ghost.rI <> Ghost.tStar - Ghost.hI) /\
  (Ghost.decI => HRO.RO.m.[Ghost.sI] = Some Ghost.hI) ==> (Mem.pk, Mem.sk) \in dkeys /\ 0 <= Exp.WO.cD /\ 0 <= Exp.WO.cH /\
  size Mem.logG <= Exp.WO.cG /\ Exp.WO.cG <= qG /\
  logs_okH Mem.logH HRO.RO.m /\ logs_okG Mem.logG GRO.RO.m /\
  (!Ghost.stop => forall x, x \in GRO.RO.m => x \in unzip1 Mem.logG) /\
  (!Ghost.stop => forall x, x \in HRO.RO.m => x \in unzip1 Mem.logH) /\
  (Mem.askH => Ghost.stop) /\ (Ghost.decI => Ghost.stop) /\ (Ghost.dI => Ghost.stop) /\
  (Mem.challenged => Ghost.rSet) /\ (Ghost.rSet => Mem.cS <> None \/ Ghost.stop) /\
  (Mem.cS <> None => Mem.challenged) /\
  (Mem.challenged => Mem.cS = Some (f Mem.pk (Mem.sStar, Ghost.tStar))) /\
  (Mem.challenged => !(Mem.sStar \in unzip1 Mem.logH)) /\
  (Mem.challenged => Mem.sStar \in HRO.RO.m => Ghost.decI /\ Ghost.sI = Mem.sStar) /\
  (Ghost.rSet => !Mem.challenged => !Ghost.decI) /\
  (Ghost.decI => Mem.challenged => Ghost.sI = Mem.sStar => Ghost.rI <> Ghost.tStar - Ghost.hI) /\
  (Ghost.decI => HRO.RO.m.[Ghost.sI] = Some Ghost.hI)].
proof.
proc; sp; if => //; inline *; sp; if => //; last by auto => /> /#.
auto => />; smt(get_setE mem_set).
qed.

local lemma inv_hashH :
  hoare[Exp(E5.O, A).WO.hashH : (Mem.pk, Mem.sk) \in dkeys /\ 0 <= Exp.WO.cD /\ 0 <= Exp.WO.cH /\
  size Mem.logG <= Exp.WO.cG /\ Exp.WO.cG <= qG /\
  logs_okH Mem.logH HRO.RO.m /\ logs_okG Mem.logG GRO.RO.m /\
  (!Ghost.stop => forall x, x \in GRO.RO.m => x \in unzip1 Mem.logG) /\
  (!Ghost.stop => forall x, x \in HRO.RO.m => x \in unzip1 Mem.logH) /\
  (Mem.askH => Ghost.stop) /\ (Ghost.decI => Ghost.stop) /\ (Ghost.dI => Ghost.stop) /\
  (Mem.challenged => Ghost.rSet) /\ (Ghost.rSet => Mem.cS <> None \/ Ghost.stop) /\
  (Mem.cS <> None => Mem.challenged) /\
  (Mem.challenged => Mem.cS = Some (f Mem.pk (Mem.sStar, Ghost.tStar))) /\
  (Mem.challenged => !(Mem.sStar \in unzip1 Mem.logH)) /\
  (Mem.challenged => Mem.sStar \in HRO.RO.m => Ghost.decI /\ Ghost.sI = Mem.sStar) /\
  (Ghost.rSet => !Mem.challenged => !Ghost.decI) /\
  (Ghost.decI => Mem.challenged => Ghost.sI = Mem.sStar => Ghost.rI <> Ghost.tStar - Ghost.hI) /\
  (Ghost.decI => HRO.RO.m.[Ghost.sI] = Some Ghost.hI) ==> (Mem.pk, Mem.sk) \in dkeys /\ 0 <= Exp.WO.cD /\ 0 <= Exp.WO.cH /\
  size Mem.logG <= Exp.WO.cG /\ Exp.WO.cG <= qG /\
  logs_okH Mem.logH HRO.RO.m /\ logs_okG Mem.logG GRO.RO.m /\
  (!Ghost.stop => forall x, x \in GRO.RO.m => x \in unzip1 Mem.logG) /\
  (!Ghost.stop => forall x, x \in HRO.RO.m => x \in unzip1 Mem.logH) /\
  (Mem.askH => Ghost.stop) /\ (Ghost.decI => Ghost.stop) /\ (Ghost.dI => Ghost.stop) /\
  (Mem.challenged => Ghost.rSet) /\ (Ghost.rSet => Mem.cS <> None \/ Ghost.stop) /\
  (Mem.cS <> None => Mem.challenged) /\
  (Mem.challenged => Mem.cS = Some (f Mem.pk (Mem.sStar, Ghost.tStar))) /\
  (Mem.challenged => !(Mem.sStar \in unzip1 Mem.logH)) /\
  (Mem.challenged => Mem.sStar \in HRO.RO.m => Ghost.decI /\ Ghost.sI = Mem.sStar) /\
  (Ghost.rSet => !Mem.challenged => !Ghost.decI) /\
  (Ghost.decI => Mem.challenged => Ghost.sI = Mem.sStar => Ghost.rI <> Ghost.tStar - Ghost.hI) /\
  (Ghost.decI => HRO.RO.m.[Ghost.sI] = Some Ghost.hI)].
proof.
proc; sp; if => //; inline *; sp; if => //; last by auto => /> /#.
if; first by auto => /> /#.
auto => />; smt(get_setE mem_set).
qed.

local lemma inv_fchallenge :
  hoare[F4(HRO.LRO).O.fchallenge : (Mem.pk, Mem.sk) \in dkeys /\ 0 <= Exp.WO.cD /\ 0 <= Exp.WO.cH /\
  size Mem.logG <= Exp.WO.cG /\ Exp.WO.cG <= qG /\
  logs_okH Mem.logH HRO.RO.m /\ logs_okG Mem.logG GRO.RO.m /\
  (!Ghost.stop => forall x, x \in GRO.RO.m => x \in unzip1 Mem.logG) /\
  (!Ghost.stop => forall x, x \in HRO.RO.m => x \in unzip1 Mem.logH) /\
  (Mem.askH => Ghost.stop) /\ (Ghost.decI => Ghost.stop) /\ (Ghost.dI => Ghost.stop) /\
  (Mem.challenged => Ghost.rSet) /\ (Ghost.rSet => Mem.cS <> None \/ Ghost.stop) /\
  (Mem.cS <> None => Mem.challenged) /\
  (Mem.challenged => Mem.cS = Some (f Mem.pk (Mem.sStar, Ghost.tStar))) /\
  (Mem.challenged => !(Mem.sStar \in unzip1 Mem.logH)) /\
  (Mem.challenged => Mem.sStar \in HRO.RO.m => Ghost.decI /\ Ghost.sI = Mem.sStar) /\
  (Ghost.rSet => !Mem.challenged => !Ghost.decI) /\
  (Ghost.decI => Mem.challenged => Ghost.sI = Mem.sStar => Ghost.rI <> Ghost.tStar - Ghost.hI) /\
  (Ghost.decI => HRO.RO.m.[Ghost.sI] = Some Ghost.hI) ==> (Mem.pk, Mem.sk) \in dkeys /\ 0 <= Exp.WO.cD /\ 0 <= Exp.WO.cH /\
  size Mem.logG <= Exp.WO.cG /\ Exp.WO.cG <= qG /\
  logs_okH Mem.logH HRO.RO.m /\ logs_okG Mem.logG GRO.RO.m /\
  (!Ghost.stop => forall x, x \in GRO.RO.m => x \in unzip1 Mem.logG) /\
  (!Ghost.stop => forall x, x \in HRO.RO.m => x \in unzip1 Mem.logH) /\
  (Mem.askH => Ghost.stop) /\ (Ghost.decI => Ghost.stop) /\ (Ghost.dI => Ghost.stop) /\
  (Mem.challenged => Ghost.rSet) /\ (Ghost.rSet => Mem.cS <> None \/ Ghost.stop) /\
  (Mem.cS <> None => Mem.challenged) /\
  (Mem.challenged => Mem.cS = Some (f Mem.pk (Mem.sStar, Ghost.tStar))) /\
  (Mem.challenged => !(Mem.sStar \in unzip1 Mem.logH)) /\
  (Mem.challenged => Mem.sStar \in HRO.RO.m => Ghost.decI /\ Ghost.sI = Mem.sStar) /\
  (Ghost.rSet => !Mem.challenged => !Ghost.decI) /\
  (Ghost.decI => Mem.challenged => Ghost.sI = Mem.sStar => Ghost.rI <> Ghost.tStar - Ghost.hI) /\
  (Ghost.decI => HRO.RO.m.[Ghost.sI] = Some Ghost.hI)].
proof.
proc; inline *; sp; if; last by auto.
sp; if; last by auto.
seq 3 : ((Mem.pk, Mem.sk) \in dkeys /\ 0 <= Exp.WO.cD /\ 0 <= Exp.WO.cH /\
  size Mem.logG <= Exp.WO.cG /\ Exp.WO.cG <= qG /\
  logs_okH Mem.logH HRO.RO.m /\ logs_okG Mem.logG GRO.RO.m /\
  (!Ghost.stop => forall x, x \in GRO.RO.m => x \in unzip1 Mem.logG) /\
  (!Ghost.stop => forall x, x \in HRO.RO.m => x \in unzip1 Mem.logH) /\
  (Mem.askH => Ghost.stop) /\ (Ghost.decI => Ghost.stop) /\ (Ghost.dI => Ghost.stop) /\
  (Mem.challenged => Ghost.rSet) /\ (Ghost.rSet => Mem.cS <> None \/ Ghost.stop) /\
  (Mem.cS <> None => Mem.challenged) /\
  (Mem.challenged => Mem.cS = Some (f Mem.pk (Mem.sStar, Ghost.tStar))) /\
  (Mem.challenged => !(Mem.sStar \in unzip1 Mem.logH)) /\
  (Mem.challenged => Mem.sStar \in HRO.RO.m => Ghost.decI /\ Ghost.sI = Mem.sStar) /\
  (Ghost.rSet => !Mem.challenged => !Ghost.decI) /\
  (Ghost.decI => Mem.challenged => Ghost.sI = Mem.sStar => Ghost.rI <> Ghost.tStar - Ghost.hI) /\
  (Ghost.decI => HRO.RO.m.[Ghost.sI] = Some Ghost.hI) /\ !Ghost.stop /\ Mem.cS = None /\ !Ghost.rSet /\ !Mem.challenged); 1: by auto => /> /#.
if.
+ by auto => /> /#.
by auto => /> /#.
qed.

local lemma inv_challenge :
  hoare[Exp(E5.O, A).WO.challenge : (Mem.pk, Mem.sk) \in dkeys /\ 0 <= Exp.WO.cD /\ 0 <= Exp.WO.cH /\
  size Mem.logG <= Exp.WO.cG /\ Exp.WO.cG <= qG /\
  logs_okH Mem.logH HRO.RO.m /\ logs_okG Mem.logG GRO.RO.m /\
  (!Ghost.stop => forall x, x \in GRO.RO.m => x \in unzip1 Mem.logG) /\
  (!Ghost.stop => forall x, x \in HRO.RO.m => x \in unzip1 Mem.logH) /\
  (Mem.askH => Ghost.stop) /\ (Ghost.decI => Ghost.stop) /\ (Ghost.dI => Ghost.stop) /\
  (Mem.challenged => Ghost.rSet) /\ (Ghost.rSet => Mem.cS <> None \/ Ghost.stop) /\
  (Mem.cS <> None => Mem.challenged) /\
  (Mem.challenged => Mem.cS = Some (f Mem.pk (Mem.sStar, Ghost.tStar))) /\
  (Mem.challenged => !(Mem.sStar \in unzip1 Mem.logH)) /\
  (Mem.challenged => Mem.sStar \in HRO.RO.m => Ghost.decI /\ Ghost.sI = Mem.sStar) /\
  (Ghost.rSet => !Mem.challenged => !Ghost.decI) /\
  (Ghost.decI => Mem.challenged => Ghost.sI = Mem.sStar => Ghost.rI <> Ghost.tStar - Ghost.hI) /\
  (Ghost.decI => HRO.RO.m.[Ghost.sI] = Some Ghost.hI) ==> (Mem.pk, Mem.sk) \in dkeys /\ 0 <= Exp.WO.cD /\ 0 <= Exp.WO.cH /\
  size Mem.logG <= Exp.WO.cG /\ Exp.WO.cG <= qG /\
  logs_okH Mem.logH HRO.RO.m /\ logs_okG Mem.logG GRO.RO.m /\
  (!Ghost.stop => forall x, x \in GRO.RO.m => x \in unzip1 Mem.logG) /\
  (!Ghost.stop => forall x, x \in HRO.RO.m => x \in unzip1 Mem.logH) /\
  (Mem.askH => Ghost.stop) /\ (Ghost.decI => Ghost.stop) /\ (Ghost.dI => Ghost.stop) /\
  (Mem.challenged => Ghost.rSet) /\ (Ghost.rSet => Mem.cS <> None \/ Ghost.stop) /\
  (Mem.cS <> None => Mem.challenged) /\
  (Mem.challenged => Mem.cS = Some (f Mem.pk (Mem.sStar, Ghost.tStar))) /\
  (Mem.challenged => !(Mem.sStar \in unzip1 Mem.logH)) /\
  (Mem.challenged => Mem.sStar \in HRO.RO.m => Ghost.decI /\ Ghost.sI = Mem.sStar) /\
  (Ghost.rSet => !Mem.challenged => !Ghost.decI) /\
  (Ghost.decI => Mem.challenged => Ghost.sI = Mem.sStar => Ghost.rI <> Ghost.tStar - Ghost.hI) /\
  (Ghost.decI => HRO.RO.m.[Ghost.sI] = Some Ghost.hI)].
proof.
proc; inline *; sp; if => //; last by auto.
sp; if => //; last by auto.
seq 3 : ((Mem.pk, Mem.sk) \in dkeys /\ 0 <= Exp.WO.cD /\ 0 <= Exp.WO.cH /\
  size Mem.logG <= Exp.WO.cG /\ Exp.WO.cG <= qG /\
  logs_okH Mem.logH HRO.RO.m /\ logs_okG Mem.logG GRO.RO.m /\
  (!Ghost.stop => forall x, x \in GRO.RO.m => x \in unzip1 Mem.logG) /\
  (!Ghost.stop => forall x, x \in HRO.RO.m => x \in unzip1 Mem.logH) /\
  (Mem.askH => Ghost.stop) /\ (Ghost.decI => Ghost.stop) /\ (Ghost.dI => Ghost.stop) /\
  (Mem.challenged => Ghost.rSet) /\ (Ghost.rSet => Mem.cS <> None \/ Ghost.stop) /\
  (Mem.cS <> None => Mem.challenged) /\
  (Mem.challenged => Mem.cS = Some (f Mem.pk (Mem.sStar, Ghost.tStar))) /\
  (Mem.challenged => !(Mem.sStar \in unzip1 Mem.logH)) /\
  (Mem.challenged => Mem.sStar \in HRO.RO.m => Ghost.decI /\ Ghost.sI = Mem.sStar) /\
  (Ghost.rSet => !Mem.challenged => !Ghost.decI) /\
  (Ghost.decI => Mem.challenged => Ghost.sI = Mem.sStar => Ghost.rI <> Ghost.tStar - Ghost.hI) /\
  (Ghost.decI => HRO.RO.m.[Ghost.sI] = Some Ghost.hI) /\ !Ghost.stop /\ Mem.cS = None /\ !Ghost.rSet /\ !Mem.challenged); 1: by auto => /> /#.
if.
+ by auto => /> /#.
by auto => /> /#.
qed.

local lemma inv_inS :
  hoare[Exp(E5.O, A).WO.inS : (Mem.pk, Mem.sk) \in dkeys /\ 0 <= Exp.WO.cD /\ 0 <= Exp.WO.cH /\
  size Mem.logG <= Exp.WO.cG /\ Exp.WO.cG <= qG /\
  logs_okH Mem.logH HRO.RO.m /\ logs_okG Mem.logG GRO.RO.m /\
  (!Ghost.stop => forall x, x \in GRO.RO.m => x \in unzip1 Mem.logG) /\
  (!Ghost.stop => forall x, x \in HRO.RO.m => x \in unzip1 Mem.logH) /\
  (Mem.askH => Ghost.stop) /\ (Ghost.decI => Ghost.stop) /\ (Ghost.dI => Ghost.stop) /\
  (Mem.challenged => Ghost.rSet) /\ (Ghost.rSet => Mem.cS <> None \/ Ghost.stop) /\
  (Mem.cS <> None => Mem.challenged) /\
  (Mem.challenged => Mem.cS = Some (f Mem.pk (Mem.sStar, Ghost.tStar))) /\
  (Mem.challenged => !(Mem.sStar \in unzip1 Mem.logH)) /\
  (Mem.challenged => Mem.sStar \in HRO.RO.m => Ghost.decI /\ Ghost.sI = Mem.sStar) /\
  (Ghost.rSet => !Mem.challenged => !Ghost.decI) /\
  (Ghost.decI => Mem.challenged => Ghost.sI = Mem.sStar => Ghost.rI <> Ghost.tStar - Ghost.hI) /\
  (Ghost.decI => HRO.RO.m.[Ghost.sI] = Some Ghost.hI) ==> (Mem.pk, Mem.sk) \in dkeys /\ 0 <= Exp.WO.cD /\ 0 <= Exp.WO.cH /\
  size Mem.logG <= Exp.WO.cG /\ Exp.WO.cG <= qG /\
  logs_okH Mem.logH HRO.RO.m /\ logs_okG Mem.logG GRO.RO.m /\
  (!Ghost.stop => forall x, x \in GRO.RO.m => x \in unzip1 Mem.logG) /\
  (!Ghost.stop => forall x, x \in HRO.RO.m => x \in unzip1 Mem.logH) /\
  (Mem.askH => Ghost.stop) /\ (Ghost.decI => Ghost.stop) /\ (Ghost.dI => Ghost.stop) /\
  (Mem.challenged => Ghost.rSet) /\ (Ghost.rSet => Mem.cS <> None \/ Ghost.stop) /\
  (Mem.cS <> None => Mem.challenged) /\
  (Mem.challenged => Mem.cS = Some (f Mem.pk (Mem.sStar, Ghost.tStar))) /\
  (Mem.challenged => !(Mem.sStar \in unzip1 Mem.logH)) /\
  (Mem.challenged => Mem.sStar \in HRO.RO.m => Ghost.decI /\ Ghost.sI = Mem.sStar) /\
  (Ghost.rSet => !Mem.challenged => !Ghost.decI) /\
  (Ghost.decI => Mem.challenged => Ghost.sI = Mem.sStar => Ghost.rI <> Ghost.tStar - Ghost.hI) /\
  (Ghost.decI => HRO.RO.m.[Ghost.sI] = Some Ghost.hI)].
proof. by proc; inline *; auto. qed.

local lemma inv_reveal :
  hoare[Exp(E5.O, A).WO.reveal : (Mem.pk, Mem.sk) \in dkeys /\ 0 <= Exp.WO.cD /\ 0 <= Exp.WO.cH /\
  size Mem.logG <= Exp.WO.cG /\ Exp.WO.cG <= qG /\
  logs_okH Mem.logH HRO.RO.m /\ logs_okG Mem.logG GRO.RO.m /\
  (!Ghost.stop => forall x, x \in GRO.RO.m => x \in unzip1 Mem.logG) /\
  (!Ghost.stop => forall x, x \in HRO.RO.m => x \in unzip1 Mem.logH) /\
  (Mem.askH => Ghost.stop) /\ (Ghost.decI => Ghost.stop) /\ (Ghost.dI => Ghost.stop) /\
  (Mem.challenged => Ghost.rSet) /\ (Ghost.rSet => Mem.cS <> None \/ Ghost.stop) /\
  (Mem.cS <> None => Mem.challenged) /\
  (Mem.challenged => Mem.cS = Some (f Mem.pk (Mem.sStar, Ghost.tStar))) /\
  (Mem.challenged => !(Mem.sStar \in unzip1 Mem.logH)) /\
  (Mem.challenged => Mem.sStar \in HRO.RO.m => Ghost.decI /\ Ghost.sI = Mem.sStar) /\
  (Ghost.rSet => !Mem.challenged => !Ghost.decI) /\
  (Ghost.decI => Mem.challenged => Ghost.sI = Mem.sStar => Ghost.rI <> Ghost.tStar - Ghost.hI) /\
  (Ghost.decI => HRO.RO.m.[Ghost.sI] = Some Ghost.hI) ==> (Mem.pk, Mem.sk) \in dkeys /\ 0 <= Exp.WO.cD /\ 0 <= Exp.WO.cH /\
  size Mem.logG <= Exp.WO.cG /\ Exp.WO.cG <= qG /\
  logs_okH Mem.logH HRO.RO.m /\ logs_okG Mem.logG GRO.RO.m /\
  (!Ghost.stop => forall x, x \in GRO.RO.m => x \in unzip1 Mem.logG) /\
  (!Ghost.stop => forall x, x \in HRO.RO.m => x \in unzip1 Mem.logH) /\
  (Mem.askH => Ghost.stop) /\ (Ghost.decI => Ghost.stop) /\ (Ghost.dI => Ghost.stop) /\
  (Mem.challenged => Ghost.rSet) /\ (Ghost.rSet => Mem.cS <> None \/ Ghost.stop) /\
  (Mem.cS <> None => Mem.challenged) /\
  (Mem.challenged => Mem.cS = Some (f Mem.pk (Mem.sStar, Ghost.tStar))) /\
  (Mem.challenged => !(Mem.sStar \in unzip1 Mem.logH)) /\
  (Mem.challenged => Mem.sStar \in HRO.RO.m => Ghost.decI /\ Ghost.sI = Mem.sStar) /\
  (Ghost.rSet => !Mem.challenged => !Ghost.decI) /\
  (Ghost.decI => Mem.challenged => Ghost.sI = Mem.sStar => Ghost.rI <> Ghost.tStar - Ghost.hI) /\
  (Ghost.decI => HRO.RO.m.[Ghost.sI] = Some Ghost.hI)].
proof. by proc; inline *; auto. qed.

local lemma inv_dec :
  hoare[Exp(E5.O, A).WO.dec : (Mem.pk, Mem.sk) \in dkeys /\ 0 <= Exp.WO.cD /\ 0 <= Exp.WO.cH /\
  size Mem.logG <= Exp.WO.cG /\ Exp.WO.cG <= qG /\
  logs_okH Mem.logH HRO.RO.m /\ logs_okG Mem.logG GRO.RO.m /\
  (!Ghost.stop => forall x, x \in GRO.RO.m => x \in unzip1 Mem.logG) /\
  (!Ghost.stop => forall x, x \in HRO.RO.m => x \in unzip1 Mem.logH) /\
  (Mem.askH => Ghost.stop) /\ (Ghost.decI => Ghost.stop) /\ (Ghost.dI => Ghost.stop) /\
  (Mem.challenged => Ghost.rSet) /\ (Ghost.rSet => Mem.cS <> None \/ Ghost.stop) /\
  (Mem.cS <> None => Mem.challenged) /\
  (Mem.challenged => Mem.cS = Some (f Mem.pk (Mem.sStar, Ghost.tStar))) /\
  (Mem.challenged => !(Mem.sStar \in unzip1 Mem.logH)) /\
  (Mem.challenged => Mem.sStar \in HRO.RO.m => Ghost.decI /\ Ghost.sI = Mem.sStar) /\
  (Ghost.rSet => !Mem.challenged => !Ghost.decI) /\
  (Ghost.decI => Mem.challenged => Ghost.sI = Mem.sStar => Ghost.rI <> Ghost.tStar - Ghost.hI) /\
  (Ghost.decI => HRO.RO.m.[Ghost.sI] = Some Ghost.hI) ==> (Mem.pk, Mem.sk) \in dkeys /\ 0 <= Exp.WO.cD /\ 0 <= Exp.WO.cH /\
  size Mem.logG <= Exp.WO.cG /\ Exp.WO.cG <= qG /\
  logs_okH Mem.logH HRO.RO.m /\ logs_okG Mem.logG GRO.RO.m /\
  (!Ghost.stop => forall x, x \in GRO.RO.m => x \in unzip1 Mem.logG) /\
  (!Ghost.stop => forall x, x \in HRO.RO.m => x \in unzip1 Mem.logH) /\
  (Mem.askH => Ghost.stop) /\ (Ghost.decI => Ghost.stop) /\ (Ghost.dI => Ghost.stop) /\
  (Mem.challenged => Ghost.rSet) /\ (Ghost.rSet => Mem.cS <> None \/ Ghost.stop) /\
  (Mem.cS <> None => Mem.challenged) /\
  (Mem.challenged => Mem.cS = Some (f Mem.pk (Mem.sStar, Ghost.tStar))) /\
  (Mem.challenged => !(Mem.sStar \in unzip1 Mem.logH)) /\
  (Mem.challenged => Mem.sStar \in HRO.RO.m => Ghost.decI /\ Ghost.sI = Mem.sStar) /\
  (Ghost.rSet => !Mem.challenged => !Ghost.decI) /\
  (Ghost.decI => Mem.challenged => Ghost.sI = Mem.sStar => Ghost.rI <> Ghost.tStar - Ghost.hI) /\
  (Ghost.decI => HRO.RO.m.[Ghost.sI] = Some Ghost.hI)].
proof.
proc; sp; if => //; inline E5.O.fdec; sp; if => //; last by auto => /> /#.
if; last by if => //; auto => /> /#.
if; last by auto => /> /#.
inline *.
auto => />; smt(get_setE get_set_sameE mem_set fiK HTag.subrK).
qed.

local lemma inv_E5 : hoare[Exp(E5.O, A).main : true ==> (Mem.pk, Mem.sk) \in dkeys /\ 0 <= Exp.WO.cD /\ 0 <= Exp.WO.cH /\
  size Mem.logG <= Exp.WO.cG /\ Exp.WO.cG <= qG /\
  logs_okH Mem.logH HRO.RO.m /\ logs_okG Mem.logG GRO.RO.m /\
  (!Ghost.stop => forall x, x \in GRO.RO.m => x \in unzip1 Mem.logG) /\
  (!Ghost.stop => forall x, x \in HRO.RO.m => x \in unzip1 Mem.logH) /\
  (Mem.askH => Ghost.stop) /\ (Ghost.decI => Ghost.stop) /\ (Ghost.dI => Ghost.stop) /\
  (Mem.challenged => Ghost.rSet) /\ (Ghost.rSet => Mem.cS <> None \/ Ghost.stop) /\
  (Mem.cS <> None => Mem.challenged) /\
  (Mem.challenged => Mem.cS = Some (f Mem.pk (Mem.sStar, Ghost.tStar))) /\
  (Mem.challenged => !(Mem.sStar \in unzip1 Mem.logH)) /\
  (Mem.challenged => Mem.sStar \in HRO.RO.m => Ghost.decI /\ Ghost.sI = Mem.sStar) /\
  (Ghost.rSet => !Mem.challenged => !Ghost.decI) /\
  (Ghost.decI => Mem.challenged => Ghost.sI = Mem.sStar => Ghost.rI <> Ghost.tStar - Ghost.hI) /\
  (Ghost.decI => HRO.RO.m.[Ghost.sI] = Some Ghost.hI)].
proof.
proc; call (: (Mem.pk, Mem.sk) \in dkeys /\ 0 <= Exp.WO.cD /\ 0 <= Exp.WO.cH /\
  size Mem.logG <= Exp.WO.cG /\ Exp.WO.cG <= qG /\
  logs_okH Mem.logH HRO.RO.m /\ logs_okG Mem.logG GRO.RO.m /\
  (!Ghost.stop => forall x, x \in GRO.RO.m => x \in unzip1 Mem.logG) /\
  (!Ghost.stop => forall x, x \in HRO.RO.m => x \in unzip1 Mem.logH) /\
  (Mem.askH => Ghost.stop) /\ (Ghost.decI => Ghost.stop) /\ (Ghost.dI => Ghost.stop) /\
  (Mem.challenged => Ghost.rSet) /\ (Ghost.rSet => Mem.cS <> None \/ Ghost.stop) /\
  (Mem.cS <> None => Mem.challenged) /\
  (Mem.challenged => Mem.cS = Some (f Mem.pk (Mem.sStar, Ghost.tStar))) /\
  (Mem.challenged => !(Mem.sStar \in unzip1 Mem.logH)) /\
  (Mem.challenged => Mem.sStar \in HRO.RO.m => Ghost.decI /\ Ghost.sI = Mem.sStar) /\
  (Ghost.rSet => !Mem.challenged => !Ghost.decI) /\
  (Ghost.decI => Mem.challenged => Ghost.sI = Mem.sStar => Ghost.rI <> Ghost.tStar - Ghost.hI) /\
  (Ghost.decI => HRO.RO.m.[Ghost.sI] = Some Ghost.hI)).
+ exact inv_hashG.
+ exact inv_hashH.
+ exact inv_challenge.
+ exact inv_inS.
+ exact inv_dec.
+ exact inv_reveal.
inline *; auto => />.
by move=> [pk sk] hk i _ /=; rewrite hk qG_ge0 /=; smt(mem_empty).
qed.

(* The failure events of E5, as seen by the fel tactic: at the i-th Dec
   query (the flag, or the deferred rStar hitting the G log when that
   query evaluated H at sStar) and at the challenge's preH cut. *)
op evDec (bad challenged decI : bool) (sI sStar : gtag) (tStar hI : htag)
         (logG : (htag * gtag) list) : bool =
  bad \/ (challenged /\ decI /\ sI = sStar /\ (tStar - hI) \in unzip1 logG).

op evChal (rSet challenged : bool) (rStar : htag) (logG : (htag * gtag) list) : bool =
  rSet /\ !challenged /\ rStar \in unzip1 logG.

local lemma ph_fchal :
  phoare[F4(HRO.LRO).O.fchallenge :
           (Mem.pk, Mem.sk) \in dkeys /\ 0 <= Exp.WO.cD /\ 0 <= Exp.WO.cH /\
  size Mem.logG <= Exp.WO.cG /\ Exp.WO.cG <= qG /\
  logs_okH Mem.logH HRO.RO.m /\ logs_okG Mem.logG GRO.RO.m /\
  (!Ghost.stop => forall x, x \in GRO.RO.m => x \in unzip1 Mem.logG) /\
  (!Ghost.stop => forall x, x \in HRO.RO.m => x \in unzip1 Mem.logH) /\
  (Mem.askH => Ghost.stop) /\ (Ghost.decI => Ghost.stop) /\ (Ghost.dI => Ghost.stop) /\
  (Mem.challenged => Ghost.rSet) /\ (Ghost.rSet => Mem.cS <> None \/ Ghost.stop) /\
  (Mem.cS <> None => Mem.challenged) /\
  (Mem.challenged => Mem.cS = Some (f Mem.pk (Mem.sStar, Ghost.tStar))) /\
  (Mem.challenged => !(Mem.sStar \in unzip1 Mem.logH)) /\
  (Mem.challenged => Mem.sStar \in HRO.RO.m => Ghost.decI /\ Ghost.sI = Mem.sStar) /\
  (Ghost.rSet => !Mem.challenged => !Ghost.decI) /\
  (Ghost.decI => Mem.challenged => Ghost.sI = Mem.sStar => Ghost.rI <> Ghost.tStar - Ghost.hI) /\
  (Ghost.decI => HRO.RO.m.[Ghost.sI] = Some Ghost.hI) /\ !evChal Ghost.rSet Mem.challenged Ghost.rStar Mem.logG /\ Mem.cS = None /\ !Ghost.stop
           ==> evChal Ghost.rSet Mem.challenged Ghost.rStar Mem.logG] <= (qG%r / cardHtag%r).
proof.
proc; inline *; sp; rcondt 1; 1: by auto.
rcondt 1; 1: by auto.
seq 3 : true 1%r (qG%r / cardHtag%r) 0%r 0%r
        (size Mem.logG <= qG /\ !Ghost.rSet /\ !Mem.challenged) => //.
+ by auto => /> /#.
+ if.
  + rcondt 2; 1: by auto.
    wp; rnd; skip => /> &hr hsz _ _ _.
    apply (ler_trans (mu dhtag (mem (unzip1 Mem.logG{hr})))).
    + by apply mu_le => r _ /=; rewrite /evChal.
    apply (ler_trans ((size (unzip1 Mem.logG{hr}))%r / cardHtag%r)).
    + have -> : (size (unzip1 Mem.logG{hr}))%r / cardHtag%r
                = (size (unzip1 Mem.logG{hr}))%r * (1%r / cardHtag%r) by smt().
      by apply (mu_mem_le_mu1 dhtag (unzip1 Mem.logG{hr}) (1%r / cardHtag%r)) => x; rewrite dhtag1E.
    by rewrite size_map; smt(cardHtag_gt0).
  by hoare; auto => />; smt(cardHtag_gt0 qG_ge0).
qed.

local lemma ph_dec :
  phoare[Exp(E5.O, A).WO.dec :
           (Mem.pk, Mem.sk) \in dkeys /\ 0 <= Exp.WO.cD /\ 0 <= Exp.WO.cH /\
  size Mem.logG <= Exp.WO.cG /\ Exp.WO.cG <= qG /\
  logs_okH Mem.logH HRO.RO.m /\ logs_okG Mem.logG GRO.RO.m /\
  (!Ghost.stop => forall x, x \in GRO.RO.m => x \in unzip1 Mem.logG) /\
  (!Ghost.stop => forall x, x \in HRO.RO.m => x \in unzip1 Mem.logH) /\
  (Mem.askH => Ghost.stop) /\ (Ghost.decI => Ghost.stop) /\ (Ghost.dI => Ghost.stop) /\
  (Mem.challenged => Ghost.rSet) /\ (Ghost.rSet => Mem.cS <> None \/ Ghost.stop) /\
  (Mem.cS <> None => Mem.challenged) /\
  (Mem.challenged => Mem.cS = Some (f Mem.pk (Mem.sStar, Ghost.tStar))) /\
  (Mem.challenged => !(Mem.sStar \in unzip1 Mem.logH)) /\
  (Mem.challenged => Mem.sStar \in HRO.RO.m => Ghost.decI /\ Ghost.sI = Mem.sStar) /\
  (Ghost.rSet => !Mem.challenged => !Ghost.decI) /\
  (Ghost.decI => Mem.challenged => Ghost.sI = Mem.sStar => Ghost.rI <> Ghost.tStar - Ghost.hI) /\
  (Ghost.decI => HRO.RO.m.[Ghost.sI] = Some Ghost.hI) /\ !evDec Mem.bad Mem.challenged Ghost.decI Ghost.sI Mem.sStar Ghost.tStar Ghost.hI Mem.logG /\ Exp.WO.cD = Ghost.i /\ !Ghost.stop
           ==> evDec Mem.bad Mem.challenged Ghost.decI Ghost.sI Mem.sStar Ghost.tStar Ghost.hI Mem.logG] <= ((2 * qG)%r / cardHtag%r + 1%r / cardRed%r).
proof.
proc; sp; if; last by hoare; auto => /> /#.
inline E5.O.fdec; sp; rcondt 1; 1: by auto.
rcondt 1; 1: by auto.
if; last by hoare; auto => /> /#.
inline *; sp.
exists* HRO.RO.m; elim* => hm0.
seq 3 : (x \notin hm0 /\
         (t - r0 \in unzip1 Mem.logG \/
          (Mem.challenged /\ s = Mem.sStar /\ Ghost.tStar - r0 \in unzip1 Mem.logG)))
        ((2 * qG)%r / cardHtag%r) 1%r 1%r (1%r / cardRed%r)
        ((Mem.pk, Mem.sk) \in dkeys /\ logs_okH Mem.logH HRO.RO.m /\ logs_okG Mem.logG GRO.RO.m /\
         size Mem.logG <= qG /\ !Ghost.stop /\ !Ghost.decI /\ !Mem.bad /\
         (forall y, y \in GRO.RO.m => y \in unzip1 Mem.logG) /\
         (forall y, y \in hm0 => y \in unzip1 Mem.logH) /\
         (Mem.challenged => Mem.sStar \notin hm0) /\
         (Mem.challenged => Mem.cS = Some (f Mem.pk (Mem.sStar, Ghost.tStar))) /\
         (s, t) = fi Mem.sk c0 /\ x = s /\ Mem.cS <> Some c0 /\
         HRO.RO.m.[x] = Some r0 /\ (x \in hm0 => HRO.RO.m = hm0)) => //.
+ by auto => />; smt(get_setE get_set_sameE mem_set).
+ case: (x \in hm0).
  + by hoare; auto => />; smt(cardHtag_gt0 qG_ge0).
  rcondt 2; 1: by auto => /> /#.
  wp; rnd; skip => /> &hr *.
  apply (ler_trans (mu dhtag (predU (fun r1 => t{hr} - r1 \in unzip1 Mem.logG{hr})
                                     (fun r1 => Ghost.tStar{hr} - r1 \in unzip1 Mem.logG{hr})))).
  + by apply mu_le => r1 _ /=; rewrite /predU get_set_sameE oget_some /#.
  apply (ler_trans (mu dhtag (fun r1 => t{hr} - r1 \in unzip1 Mem.logG{hr})
                    + mu dhtag (fun r1 => Ghost.tStar{hr} - r1 \in unzip1 Mem.logG{hr}))).
  + by rewrite mu_or; smt(ge0_mu).
  have h1 := mu_dhtag_mem_sub t{hr} (unzip1 Mem.logG{hr}).
  have h2 := mu_dhtag_mem_sub Ghost.tStar{hr} (unzip1 Mem.logG{hr}).
  apply (ler_trans _ _ _ (ler_add _ _ _ _ h1 h2)).
  rewrite size_map.
  have -> : (size Mem.logG{hr})%r / cardHtag%r + (size Mem.logG{hr})%r / cardHtag%r
            = (2 * size Mem.logG{hr})%r / cardHtag%r by smt().
  by apply div_le; smt(cardHtag_gt0).
+ case: (t - r0 \in unzip1 Mem.logG).
  + hoare; auto => />; first by smt(cardRed_gt0 invr_ge0).
    move=> &hr hk hokH hokG hsz hstop hdec hbad hgm hhm hsStar hcS hfi hne hs hhm0 hnA hin.
    have hs0 : s{hr} \in hm0 by smt().
    have hsl : s{hr} \in unzip1 Mem.logH{hr} by apply hhm.
    have hr : t{hr} - r0{hr} \in GRO.RO.m{hr}.
    + by have [y hy] := in_unzip1 _ _ hin; have := hokG _ _ hy; smt(domE).
    have hext := ext_logged Mem.pk{hr} Mem.sk{hr} Mem.logH{hr} Mem.logG{hr} HRO.RO.m{hr} GRO.RO.m{hr} c0{hr} hk hokH hokG _ _.
    + by rewrite -hfi.
    + by rewrite -hfi /= hs oget_some.
    move: hext; rewrite -hfi /= hs oget_some => hext.
    move=> r20 _; split; 1: by move=> hnin; smt().
    move=> _.
    have hneq : !(Mem.challenged{hr} /\ s{hr} = Mem.sStar{hr}) by smt().
    by rewrite hext /evDec /=; smt().
  seq 7 : (unpad (gsub s g) <> None) (1%r / cardRed%r) 1%r _ 0%r
          ((Mem.pk, Mem.sk) \in dkeys /\ logs_okH Mem.logH HRO.RO.m /\ logs_okG Mem.logG GRO.RO.m /\
           !Mem.bad /\ (s, t) = fi Mem.sk c0 /\ Mem.cS <> Some c0 /\
           HRO.RO.m.[s] = Some Ghost.hI /\ Ghost.sI = s /\ Ghost.decI /\
           x0 = t - Ghost.hI /\ x0 \in GRO.RO.m /\ g = oget GRO.RO.m.[x0] /\
           !(Mem.challenged /\ s = Mem.sStar /\ Ghost.tStar - Ghost.hI \in unzip1 Mem.logG)) => //.
  + by auto => />; smt(get_setE get_set_sameE mem_set).
  + rcondt 6; 1: by auto => /> /#.
    wp; rnd; wp; skip => /> &hr *.
    apply (ler_trans (mu dgtag (fun g => unpad (gsub s{hr} g) <> None))).
    + by apply mu_le => r2 _ /=; rewrite get_set_sameE oget_some.
    by rewrite mu_dgtag_valid_sub.
      by hoare; auto => />; smt(ext_cases cardRed_gt0).
qed.

(* ------------------------------------------------------------------ *)
(* Step 2g: the bounds on E5, by the failure-event lemma.               *)
(* ------------------------------------------------------------------ *)

(* counter / event bookkeeping, per oracle *)
local lemma cnt_dec c :
  hoare[Exp(E5.O, A).WO.dec : Exp.WO.cD = Ghost.i /\ !Ghost.stop /\ Exp.WO.cD < qD /\ c = b2i Ghost.dI /\ !Ghost.dI
        ==> c < b2i Ghost.dI].
proof.
proc; sp; rcondt 1; 1: by auto.
inline E5.O.fdec; sp; rcondt 1; 1: by auto.
rcondt 1; 1: by auto.
by if; inline *; auto => /> /#.
qed.

local lemma ev_dec b c :
  hoare[Exp(E5.O, A).WO.dec : !(Exp.WO.cD = Ghost.i /\ !Ghost.stop /\ Exp.WO.cD < qD) /\
                              evDec Mem.bad Mem.challenged Ghost.decI Ghost.sI Mem.sStar Ghost.tStar Ghost.hI Mem.logG = b /\ c = b2i Ghost.dI
        ==> evDec Mem.bad Mem.challenged Ghost.decI Ghost.sI Mem.sStar Ghost.tStar Ghost.hI Mem.logG = b /\ c <= b2i Ghost.dI].
proof.
proc; sp; if; last by auto.
inline E5.O.fdec; sp; if; last by auto => /> /#.
rcondf 1; 1: by auto => /> /#.
by if; auto => /> /#.
qed.

local lemma ev_hashG b c :
  hoare[Exp(E5.O, A).WO.hashG : (Ghost.decI => Ghost.stop) /\ evDec Mem.bad Mem.challenged Ghost.decI Ghost.sI Mem.sStar Ghost.tStar Ghost.hI Mem.logG = b /\ c = b2i Ghost.dI
        ==> evDec Mem.bad Mem.challenged Ghost.decI Ghost.sI Mem.sStar Ghost.tStar Ghost.hI Mem.logG = b /\ c <= b2i Ghost.dI].
proof.
proc; sp; if; last by auto.
inline *; sp; if; last by auto.
by auto => />; rewrite /evDec /#.
qed.

local lemma ev_hashH b c :
  hoare[Exp(E5.O, A).WO.hashH : evDec Mem.bad Mem.challenged Ghost.decI Ghost.sI Mem.sStar Ghost.tStar Ghost.hI Mem.logG = b /\ c = b2i Ghost.dI
        ==> evDec Mem.bad Mem.challenged Ghost.decI Ghost.sI Mem.sStar Ghost.tStar Ghost.hI Mem.logG = b /\ c <= b2i Ghost.dI].
proof.
proc; sp; if; last by auto.
inline *; sp; if; last by auto.
by if; auto => /> /#.
qed.

local lemma ev_fchal b c :
  hoare[F4(HRO.LRO).O.fchallenge : (Ghost.decI => Ghost.stop) /\ evDec Mem.bad Mem.challenged Ghost.decI Ghost.sI Mem.sStar Ghost.tStar Ghost.hI Mem.logG = b /\ c = b2i Ghost.dI
        ==> evDec Mem.bad Mem.challenged Ghost.decI Ghost.sI Mem.sStar Ghost.tStar Ghost.hI Mem.logG = b /\ c <= b2i Ghost.dI].
proof.
proc; inline *; sp; if; last by auto.
sp; if; last by auto.
seq 3 : (evDec Mem.bad Mem.challenged Ghost.decI Ghost.sI Mem.sStar Ghost.tStar Ghost.hI Mem.logG = b /\ c = b2i Ghost.dI /\ !Ghost.decI); 1: by auto => /> /#.
by if; auto => />; rewrite /evDec /#.
qed.

local lemma cnt_fchal c :
  hoare[F4(HRO.LRO).O.fchallenge : Mem.cS = None /\ !Ghost.stop /\ c = b2i Ghost.rSet /\
                                   (Ghost.rSet => Mem.cS <> None \/ Ghost.stop)
        ==> c < b2i Ghost.rSet].
proof.
proc; sp; rcondt 1; 1: by auto.
rcondt 1; 1: by auto.
seq 3 : (c = 0 /\ !Ghost.rSet); 1: by auto => /> /#.
by if; inline *; auto => /> /#.
qed.

local lemma evc_fchal b c :
  hoare[F4(HRO.LRO).O.fchallenge : !(Mem.cS = None /\ !Ghost.stop) /\ evChal Ghost.rSet Mem.challenged Ghost.rStar Mem.logG = b /\ c = b2i Ghost.rSet
        ==> evChal Ghost.rSet Mem.challenged Ghost.rStar Mem.logG = b /\ c <= b2i Ghost.rSet].
proof.
proc; sp; if; last by auto.
rcondf 1; 1: by auto => /> /#.
by auto.
qed.

local lemma evc_dec b c :
  hoare[Exp(E5.O, A).WO.dec : evChal Ghost.rSet Mem.challenged Ghost.rStar Mem.logG = b /\ c = b2i Ghost.rSet
        ==> evChal Ghost.rSet Mem.challenged Ghost.rStar Mem.logG = b /\ c <= b2i Ghost.rSet].
proof.
proc; sp; if; last by auto.
inline E5.O.fdec; sp; if; last by auto.
if; last by if; auto.
if; last by auto.
by inline *; auto => /> /#.
qed.

local lemma evc_hashG b c :
  hoare[Exp(E5.O, A).WO.hashG : (Ghost.rSet => Mem.cS <> None \/ Ghost.stop) /\ (Mem.cS <> None => Mem.challenged) /\
                                evChal Ghost.rSet Mem.challenged Ghost.rStar Mem.logG = b /\ c = b2i Ghost.rSet
        ==> evChal Ghost.rSet Mem.challenged Ghost.rStar Mem.logG = b /\ c <= b2i Ghost.rSet].
proof.
proc; sp; if; last by auto.
inline *; sp; if; last by auto.
by auto => />; rewrite /evChal /#.
qed.

local lemma evc_hashH b c :
  hoare[Exp(E5.O, A).WO.hashH : evChal Ghost.rSet Mem.challenged Ghost.rStar Mem.logG = b /\ c = b2i Ghost.rSet
        ==> evChal Ghost.rSet Mem.challenged Ghost.rStar Mem.logG = b /\ c <= b2i Ghost.rSet].
proof.
proc; sp; if; last by auto.
inline *; sp; if; last by auto.
by if; auto => /> /#.
qed.

local lemma fel_dec &m :
  Pr[Exp(E5.O, A).main() @ &m : evDec Mem.bad Mem.challenged Ghost.decI Ghost.sI Mem.sStar Ghost.tStar Ghost.hI Mem.logG]
  <= (2 * qG)%r / cardHtag%r + 1%r / cardRed%r.
proof.
fel 1 (b2i Ghost.dI) (fun _ => (2 * qG)%r / cardHtag%r + 1%r / cardRed%r) 1
    (evDec Mem.bad Mem.challenged Ghost.decI Ghost.sI Mem.sStar Ghost.tStar Ghost.hI Mem.logG)
    [Exp(F4(HRO.LRO).O, A).WO.dec : (Exp.WO.cD = Ghost.i /\ !Ghost.stop /\ Exp.WO.cD < qD);
     Exp(F4(HRO.LRO).O, A).WO.hashG : false;
     Exp(F4(HRO.LRO).O, A).WO.hashH : false;
     F4(HRO.LRO).O.fchallenge : false]
    ((Mem.pk, Mem.sk) \in dkeys /\ 0 <= Exp.WO.cD /\ 0 <= Exp.WO.cH /\
  size Mem.logG <= Exp.WO.cG /\ Exp.WO.cG <= qG /\
  logs_okH Mem.logH HRO.RO.m /\ logs_okG Mem.logG GRO.RO.m /\
  (!Ghost.stop => forall x, x \in GRO.RO.m => x \in unzip1 Mem.logG) /\
  (!Ghost.stop => forall x, x \in HRO.RO.m => x \in unzip1 Mem.logH) /\
  (Mem.askH => Ghost.stop) /\ (Ghost.decI => Ghost.stop) /\ (Ghost.dI => Ghost.stop) /\
  (Mem.challenged => Ghost.rSet) /\ (Ghost.rSet => Mem.cS <> None \/ Ghost.stop) /\
  (Mem.cS <> None => Mem.challenged) /\
  (Mem.challenged => Mem.cS = Some (f Mem.pk (Mem.sStar, Ghost.tStar))) /\
  (Mem.challenged => !(Mem.sStar \in unzip1 Mem.logH)) /\
  (Mem.challenged => Mem.sStar \in HRO.RO.m => Ghost.decI /\ Ghost.sI = Mem.sStar) /\
  (Ghost.rSet => !Mem.challenged => !Ghost.decI) /\
  (Ghost.decI => Mem.challenged => Ghost.sI = Mem.sStar => Ghost.rI <> Ghost.tStar - Ghost.hI) /\
  (Ghost.decI => HRO.RO.m.[Ghost.sI] = Some Ghost.hI)) => //.
+ by rewrite range_ltn // range_geq // BRA.big_cons BRA.big_nil /predT /=; smt().
+ by move=> &hr /#.
+ inline *; auto => />.
  by move=> [pk sk] hk i _ /=; rewrite hk qG_ge0 /evDec /=; smt(mem_empty).
(* dec *)
+ by conseq ph_dec => /> /#.
+ by move=> c; conseq inv_dec (cnt_dec c) => /> /#.
+ by move=> b c; conseq inv_dec (ev_dec b c) => /> /#.
(* hashG *)
+ by move=> b c; conseq inv_hashG (ev_hashG b c) => /> /#.
(* hashH *)
+ by move=> b c; conseq inv_hashH (ev_hashH b c) => /> /#.
(* challenge *)
by move=> b c; conseq inv_fchallenge (ev_fchal b c) => /> /#.
qed.

local lemma fel_chal &m :
  Pr[Exp(E5.O, A).main() @ &m : evChal Ghost.rSet Mem.challenged Ghost.rStar Mem.logG] <= qG%r / cardHtag%r.
proof.
fel 1 (b2i Ghost.rSet) (fun _ => qG%r / cardHtag%r) 1
    (evChal Ghost.rSet Mem.challenged Ghost.rStar Mem.logG)
    [F4(HRO.LRO).O.fchallenge : (Mem.cS = None /\ !Ghost.stop);
     Exp(F4(HRO.LRO).O, A).WO.dec : false;
     Exp(F4(HRO.LRO).O, A).WO.hashG : false;
     Exp(F4(HRO.LRO).O, A).WO.hashH : false]
    ((Mem.pk, Mem.sk) \in dkeys /\ 0 <= Exp.WO.cD /\ 0 <= Exp.WO.cH /\
  size Mem.logG <= Exp.WO.cG /\ Exp.WO.cG <= qG /\
  logs_okH Mem.logH HRO.RO.m /\ logs_okG Mem.logG GRO.RO.m /\
  (!Ghost.stop => forall x, x \in GRO.RO.m => x \in unzip1 Mem.logG) /\
  (!Ghost.stop => forall x, x \in HRO.RO.m => x \in unzip1 Mem.logH) /\
  (Mem.askH => Ghost.stop) /\ (Ghost.decI => Ghost.stop) /\ (Ghost.dI => Ghost.stop) /\
  (Mem.challenged => Ghost.rSet) /\ (Ghost.rSet => Mem.cS <> None \/ Ghost.stop) /\
  (Mem.cS <> None => Mem.challenged) /\
  (Mem.challenged => Mem.cS = Some (f Mem.pk (Mem.sStar, Ghost.tStar))) /\
  (Mem.challenged => !(Mem.sStar \in unzip1 Mem.logH)) /\
  (Mem.challenged => Mem.sStar \in HRO.RO.m => Ghost.decI /\ Ghost.sI = Mem.sStar) /\
  (Ghost.rSet => !Mem.challenged => !Ghost.decI) /\
  (Ghost.decI => Mem.challenged => Ghost.sI = Mem.sStar => Ghost.rI <> Ghost.tStar - Ghost.hI) /\
  (Ghost.decI => HRO.RO.m.[Ghost.sI] = Some Ghost.hI)) => //.
+ by rewrite range_ltn // range_geq // BRA.big_cons BRA.big_nil /predT /=; smt().
+ by move=> &hr /#.
+ inline *; auto => />.
  by move=> [pk sk] hk i _ /=; rewrite hk qG_ge0 /evChal /=; smt(mem_empty).
(* dec *)
+ by move=> b c; conseq inv_dec (evc_dec b c) => /> /#.
(* hashG *)
+ by move=> b c; conseq inv_hashG (evc_hashG b c) => /> /#.
(* hashH *)
+ by move=> b c; conseq inv_hashH (evc_hashH b c) => /> /#.
(* challenge *)
+ by conseq ph_fchal => /> /#.
+ by move=> c; conseq inv_fchallenge (cnt_fchal c) => /> /#.
by move=> b c; conseq inv_fchallenge (evc_fchal b c) => /> /#.
qed.

local lemma ph_main :
  phoare[Exp(E5.O, A).main : true ==> evDec Mem.bad Mem.challenged Ghost.decI Ghost.sI Mem.sStar Ghost.tStar Ghost.hI Mem.logG \/ evChal Ghost.rSet Mem.challenged Ghost.rStar Mem.logG]
  <= ((2 * qG)%r / cardHtag%r + 1%r / cardRed%r + qG%r / cardHtag%r).
proof.
bypr => &m0 _; rewrite Pr [mu_or].
by have := fel_dec &m0; have := fel_chal &m0; smt(ge0_mu).
qed.

local lemma pr_E5 &m :
  Pr[E5.distinguish() @ &m : res]
  <= (2 * qG)%r / cardHtag%r + 1%r / cardRed%r + qG%r / cardHtag%r + (qG + 1)%r / cardHtag%r.
proof.
byphoare => //; proc.
seq 1 : (evDec Mem.bad Mem.challenged Ghost.decI Ghost.sI Mem.sStar Ghost.tStar Ghost.hI Mem.logG \/ evChal Ghost.rSet Mem.challenged Ghost.rStar Mem.logG)
        ((2 * qG)%r / cardHtag%r + 1%r / cardRed%r + qG%r / cardHtag%r) 1%r
        1%r ((qG + 1)%r / cardHtag%r)
        ((Mem.pk, Mem.sk) \in dkeys /\ 0 <= Exp.WO.cD /\ 0 <= Exp.WO.cH /\
  size Mem.logG <= Exp.WO.cG /\ Exp.WO.cG <= qG /\
  logs_okH Mem.logH HRO.RO.m /\ logs_okG Mem.logG GRO.RO.m /\
  (!Ghost.stop => forall x, x \in GRO.RO.m => x \in unzip1 Mem.logG) /\
  (!Ghost.stop => forall x, x \in HRO.RO.m => x \in unzip1 Mem.logH) /\
  (Mem.askH => Ghost.stop) /\ (Ghost.decI => Ghost.stop) /\ (Ghost.dI => Ghost.stop) /\
  (Mem.challenged => Ghost.rSet) /\ (Ghost.rSet => Mem.cS <> None \/ Ghost.stop) /\
  (Mem.cS <> None => Mem.challenged) /\
  (Mem.challenged => Mem.cS = Some (f Mem.pk (Mem.sStar, Ghost.tStar))) /\
  (Mem.challenged => !(Mem.sStar \in unzip1 Mem.logH)) /\
  (Mem.challenged => Mem.sStar \in HRO.RO.m => Ghost.decI /\ Ghost.sI = Mem.sStar) /\
  (Ghost.rSet => !Mem.challenged => !Ghost.decI) /\
  (Ghost.decI => Mem.challenged => Ghost.sI = Mem.sStar => Ghost.rI <> Ghost.tStar - Ghost.hI) /\
  (Ghost.decI => HRO.RO.m.[Ghost.sI] = Some Ghost.hI)) => //.
+ by call inv_E5.
+ by call ph_main.
if.
+ case (Mem.sStar \in HRO.RO.m).
  - hoare; first by smt(cardHtag_gt0 qG_ge0).
    by inline *; auto => />; rewrite /evDec /evChal /badG; smt(get_set_sameE).
  inline *; wp; rnd; wp; skip => /> &hr.
  move=> hk _ _ hsz hcG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hev hchal hnin.
  apply (ler_trans (mu dhtag (fun h => Ghost.tStar{hr} - h \in Ghost.rI{hr} :: unzip1 Mem.logG{hr}))).
  + apply mu_le => h _ /=; rewrite get_set_sameE oget_some /badG /evDec /#.
  apply (ler_trans _ _ _ (mu_dhtag_mem_sub _ _)); apply div_le; 1: by smt(cardHtag_gt0).
  by rewrite /= size_map /#.
by hoare; auto => />; rewrite /evDec /evChal /badG /#.
qed.

(* ------------------------------------------------------------------ *)
(* Step 2h: assembling the chain.                                        *)
(* ------------------------------------------------------------------ *)

local lemma pr_bad_pos &m :
  Pr[Exp(IdealO, A).main() @ &m : Mem.bad]
  <= (max 1 qD)%r * ((qG + qD)%r / cardHtag%r + qH%r / cardGtag%r
       + ((2 * qG)%r / cardHtag%r + 1%r / cardRed%r + qG%r / cardHtag%r + (qG + 1)%r / cardHtag%r)).
proof.
rewrite (pr_E0_G1 &m).
apply (ler_trans _ _ _ (pr_G1_guess &m)).
apply ler_wpmul2l; 1: by smt().
apply (ler_trans _ _ _ (pr_guess_E3 &m)).
apply (ler_trans _ _ _ (pr_E3_E3c &m)).
rewrite Pr [mu_or].
have hpre := pr_E3c_preH &m.
have hbad : Pr[Exp(IdealO3c, A).main() @ &m : Mem.bad]
  <= (2 * qG)%r / cardHtag%r + 1%r / cardRed%r + qG%r / cardHtag%r + (qG + 1)%r / cardHtag%r.
+ rewrite (pr_E3c_F3a &m) (pr_F3a_LRO &m) (pr_F3a_F3b &m) (pr_F3b_LRO &m).
  apply (ler_trans _ _ _ (pr_E3L_O4 &m)).
  rewrite (pr_O4_O4b &m) (pr_O4b_F4 &m) (pr_F4_LRO &m).
  exact (pr_E5 &m).
smt(ge0_mu).
qed.

(* With no decryption query the flag is never raised. *)
local lemma pr_bad_zero &m :
  qD = 0 => Pr[Exp(IdealO, A).main() @ &m : Mem.bad] = 0%r.
proof.
move=> hqD; byphoare => //; hoare; proc.
call (: !Mem.bad /\ 0 <= Exp.WO.cD).
+ by proc; sp; if; [by inline *; auto | by auto].
+ by proc; sp; if; [by inline *; auto | by auto].
+ by proc; inline *; sp; if; auto.
+ by proc; inline *; auto.
+ by proc; sp; if; [by exfalso; smt() | by auto].
+ by proc; inline *; auto.
by inline *; auto.
qed.

(* Step 2: the failure event. *)
local lemma pr_bad &m :
  Pr[Exp(IdealO, A).main() @ &m : Mem.bad] <= bound.
proof.
case (qD = 0) => hqD.
+ by rewrite (pr_bad_zero &m hqD) /bound hqD /#.
have h := pr_bad_pos &m.
have hmax : (max 1 qD)%r = qD%r by smt(qD_ge0).
move: h; rewrite hmax => h.
apply (ler_trans _ _ _ h).
rewrite /bound; apply ler_wpmul2l; 1: by smt(qD_ge0).
by smt(cardHtag_gt0 cardGtag_gt0 cardRed_gt0).
qed.

lemma adv_bound &m (P : bool -> bool) :
  Pr[Exp(RealO, A).main() @ &m : P res]
  <= Pr[Exp(IdealO, A).main() @ &m : P res] + bound.
proof.
have h1 := pr_real_ideal &m P.
have h2 := pr_bad &m.
smt().
qed.

end section PROOF.
