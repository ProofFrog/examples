# ProofFrog Analysis of draft-irtf-cfrg-hybrid-kems-10

This directory contains a ProofFrog formalization of the four hybrid KEM
combiners specified in:

> CFRG, *Hybrid PQ/T Key Encapsulation Mechanisms*,
> [draft-irtf-cfrg-hybrid-kems-10](https://datatracker.ietf.org/doc/draft-irtf-cfrg-hybrid-kems/10/).

The four frameworks (draft §5.3–§5.6) each combine a post-quantum KEM
(`KEM_PQ`) with a "traditional" component — either another KEM (`KEM_T`)
or a nominal group (`NG`, draft §4) — via a key-derivation function
(`KDF`). This directory provides FrogLang scheme definitions for all
four frameworks together with mechanically checked ProofFrog proofs of
correctness, IND-CCA security, LEAK-BIND-K-{CT,PK}, and HON-BIND-K-{CT,PK}.

## Contents

- [Modelling caveats](#modelling-caveats--please-read-before-citing-these-results)
- [Scope](#scope)
- [Directory layout](#directory-layout)
- [Mapping from draft sections to files](#mapping-from-draft-sections-to-files)
- [Assumption table](#assumption-table)
- [Deviations from the draft](#deviations-from-the-draft)
- [Verification](#verification)
- [Out of scope](#out-of-scope)

## Modelling caveats — please read before citing these results

The full list of modelling caveats and departures from the draft is in
[Deviations from the draft](#deviations-from-the-draft) below. Two
caveats deserve top-of-document prominence because they materially
constrain the scope of our results:

- **Implicit rejection only.** Our `KEM.primitive` declares `Decaps`
  as total (no `bot` symbol), and the binding games therefore omit the
  CDM24 Fig. 5 `bot`-guard. Our binding results are sound for
  implicitly-rejecting KEMs (FO-style; ML-KEM) but do **not** apply to
  explicitly-rejecting KEMs without extending the primitive. See
  [Deviation 12](#deviation-12).
- **No quantum-attacker model.** ProofFrog does not distinguish
  classical from quantum adversaries. Standard-model results lift to
  quantum adversaries when the underlying assumptions hold against
  quantum adversaries; ROM results (UG/CG T-branch IND-CCA and
  seeded-form CG/CK LEAK-BIND) do **not** automatically lift to the
  QROM. See [Deviation 1](#deviation-1).

Other modelling choices — byte layouts, label packaging, KDF model
granularity, decapsulation-key representation, the C2PRI / `SDH_SS` /
`KeyGenEquiv` named assumptions, the PRG-as-RO construction used for
seeded-form CG/CK LEAK-BIND, etc. — are documented in the
[Deviations from the draft](#deviations-from-the-draft) section below.

Finally, a general caveat about the tooling: ProofFrog is a research
prototype, not a fully verified proof assistant. Its proof engine
performs game-hopping verification by canonicalizing ASTs and
discharging side conditions to Z3 / SymPy; both the canonicalization
pipeline and the FrogLang semantics it implicitly assumes are under
active development and may contain bugs. A successful `prove` run
should be read as mechanically-checked evidence that the
claimed game hops are sound under the engine's interpretation of
FrogLang, not as a fully formalised mathematical proof in the sense
of Rocq / Lean / EasyCrypt. Readers relying on these results for
high-assurance claims should additionally inspect the proof scripts
and the assumption games they cite.

**Summary of ProofFrog proofs of draft-irtf-cfrg-hybrid-kems-10**

| | [UG<br>seeded](schemes/UG/UG_seedbased.scheme) | [UG<br>expanded](schemes/UG/UG_expanded.scheme) | [UK<br>seeded](schemes/UK/UK_seedbased.scheme) | [UK<br>expanded](schemes/UK/UK_expanded.scheme) | [CG<br>seeded](schemes/CG/CG_seedbased.scheme) | [CG<br>expanded](schemes/CG/CG_expanded.scheme) | [CK<br>seeded](schemes/CK/CK_seedbased.scheme) | [CK<br>expanded](schemes/CK/CK_expanded.scheme) |
|---|---|---|---|---|---|---|---|---|
| T component | NominalGroup | NominalGroup | KEM | KEM | NominalGroup | NominalGroup | KEM | KEM |
| Combiner | Universal | Universal | Universal | Universal | C2PRI | C2PRI | C2PRI | C2PRI |
| Correctness | [✅ done](proofs/UG/UG_seedbased_Correctness.proof) | [✅ done](proofs/UG/UG_expanded_Correctness.proof) | [✅ done](proofs/UK/UK_seedbased_Correctness.proof) | [✅ done](proofs/UK/UK_expanded_Correctness.proof) | [✅ done](proofs/CG/CG_seedbased_Correctness.proof) | [✅ done](proofs/CG/CG_expanded_Correctness.proof) | [✅ done](proofs/CK/CK_seedbased_Correctness.proof) | [✅ done](proofs/CK/CK_expanded_Correctness.proof) |
| IND-CCA (PQ branch) | [✅ done](proofs/UG/UG_seedbased_INDCCA_PQ.proof) | [✅ done](proofs/UG/UG_expanded_INDCCA_PQ.proof) | [✅ done](proofs/UK/UK_seedbased_INDCCA_PQ.proof) | [✅ done](proofs/UK/UK_expanded_INDCCA_PQ.proof) | [✅ done](proofs/CG/CG_seedbased_INDCCA_PQ.proof) | [✅ done](proofs/CG/CG_expanded_INDCCA_PQ.proof) | [✅ done](proofs/CK/CK_seedbased_INDCCA_PQ.proof) | [✅ done](proofs/CK/CK_expanded_INDCCA_PQ.proof) |
| IND-CCA (T branch) | [✅ done](proofs/UG/UG_seedbased_INDCCA_T.proof) (ROM) | [✅ done](proofs/UG/UG_expanded_INDCCA_T.proof) (ROM) | [✅ done](proofs/UK/UK_seedbased_INDCCA_T.proof) | [✅ done](proofs/UK/UK_expanded_INDCCA_T.proof) | [✅ done](proofs/CG/CG_seedbased_INDCCA_T.proof) (ROM) | [✅ done](proofs/CG/CG_expanded_INDCCA_T.proof) (ROM) | [✅ done](proofs/CK/CK_seedbased_INDCCA_T.proof) | [✅ done](proofs/CK/CK_expanded_INDCCA_T.proof) |
| LEAK-BIND-K-CT (std model) | [✅ done](proofs/UG/UG_seedbased_LEAK_BIND_K_CT.proof) | [✅ done](proofs/UG/UG_expanded_LEAK_BIND_K_CT.proof) | [✅ done](proofs/UK/UK_seedbased_LEAK_BIND_K_CT.proof) | [✅ done](proofs/UK/UK_expanded_LEAK_BIND_K_CT.proof) | ⚠️ unproven | [✅ done](proofs/CG/CG_expanded_LEAK_BIND_K_CT.proof) | ⚠️ unproven | [✅ done](proofs/CK/CK_expanded_LEAK_BIND_K_CT.proof) |
| LEAK-BIND-K-PK (std model) | [✅ done](proofs/UG/UG_seedbased_LEAK_BIND_K_PK.proof) | [✅ done](proofs/UG/UG_expanded_LEAK_BIND_K_PK.proof) | [✅ done](proofs/UK/UK_seedbased_LEAK_BIND_K_PK.proof) | [✅ done](proofs/UK/UK_expanded_LEAK_BIND_K_PK.proof) | ⚠️ unproven | [✅ done](proofs/CG/CG_expanded_LEAK_BIND_K_PK.proof) | ⚠️ unproven | [✅ done](proofs/CK/CK_expanded_LEAK_BIND_K_PK.proof) |
| LEAK-BIND-K-CT (PRG as ROM) | n/a | n/a | n/a | n/a | [✅ done](proofs/CG/CG_seedbased_LEAK_BIND_K_CT.proof) | n/a | [✅ done](proofs/CK/CK_seedbased_LEAK_BIND_K_CT.proof) | n/a |
| LEAK-BIND-K-PK (PRG as ROM) | n/a | n/a | n/a | n/a | [✅ done](proofs/CG/CG_seedbased_LEAK_BIND_K_PK.proof) | n/a | [✅ done](proofs/CK/CK_seedbased_LEAK_BIND_K_PK.proof) | n/a |
| HON-BIND-K-CT (std model) | implied | implied | implied | implied | [✅ done](proofs/CG/CG_seedbased_HON_BIND_K_CT.proof) | implied | [✅ done](proofs/CK/CK_seedbased_HON_BIND_K_CT.proof) | implied |
| HON-BIND-K-PK (std model) | implied | implied | implied | implied | [✅ done](proofs/CG/CG_seedbased_HON_BIND_K_PK.proof) | implied | [✅ done](proofs/CK/CK_seedbased_HON_BIND_K_PK.proof) | implied |

For each of the four frameworks (UG, UK, CG, CK), we provide:

1. A **seed-form** scheme matching draft §5.2's primary definition where
   `dk = seed` and Decaps re-runs `expandDecapsKey*(seed)` at every call.
2. An **expanded-form** scheme variant in which `dk` is the expanded
   keypair tuple. The draft §5.2 permits this expansion as an
   implementation cache. The expanded form is used to mechanise the
   standard-model LEAK-BIND results, which we have not been able to
   mechanise in the seed form under standard PRGSec / KGE / KDF-CR /
   KEM_PQ-binding assumptions (see [Deviation 6](#deviation-6) below).
3. A **correctness** proof.
4. **Two complementary IND-CCA proofs** per framework — one assuming
   `KEM_PQ` is IND-CCA, one assuming the traditional component is
   secure (IND-CCA of `KEM_T` for UK/CK; an SDH-style assumption on
   `NG` for UG/CG).
5. **LEAK-BIND-K-{CT, PK}** in both seed and expanded forms (UG/UK seed
   form is mechanisable directly; CG/CK seed form uses the PRG-as-RO
   construction of [Deviation 7](#deviation-7)).
6. **HON-BIND-K-{CT, PK}** for CG/CK in seed form (UG/UK get HON-BIND
   for free from LEAK-BIND via the generic implications in
   [`proofs/Generic/`](proofs/Generic/)).

## Directory layout

| Path | Contents |
|------|----------|
| [`primitives/`](primitives/) | `KEM`, `NominalGroup`, `KDF`, `PRG`, `Label`, `HashInputPacking` |
| [`games/KEM/`](games/KEM/) | `INDCCA`, `INDCCA_ROM`, `Correctness`, `CorrectnessWithDK`, `KeyGenEquiv`, `C2PRI`, plus the four binding games (and their ROM variants) |
| [`games/Group/`](games/Group/) | `SDH`, `SDH_SS`, `NGCorrectness`, `RandomScalarDist` |
| [`games/KDF/`](games/KDF/) | `KDFCollisionResistance`, `KDFFirstKeyPRF`, `KDFSecondKeyPRF`, `KDFPRFSec` |
| [`games/PRG/`](games/PRG/) | `PRGSec` |
| [`games/ROM/`](games/ROM/) | `LazyROTwoViewsExcluded[Programmed]`, `LazyROTwoSeeded`, `CGLazyROTwoSeeded` (statistical helper games) |
| [`schemes/{UG,UK,CG,CK}/`](schemes/) | `*_seedbased.scheme`, `*_expanded.scheme`; helper RO-flavoured PRG/KDF wrappers |
| [`schemes/Helpers/`](schemes/Helpers/) | `SeededKEMWrapper.scheme` |
| [`proofs/{UG,UK,CG,CK}/`](proofs/) | All correctness, IND-CCA, and binding proofs |
| [`proofs/Generic/`](proofs/Generic/) | `LEAK_implies_HON_BIND_K_{CT,PK}` |

## Mapping from draft sections to files

| Draft section | File |
|---|---|
| §4 (Nominal groups) | [`primitives/NominalGroup.primitive`](primitives/NominalGroup.primitive) |
| §5.2 (Seed-form decapsulation key) | All `*_seedbased.scheme` files |
| §5.3 (UniversalCombiner with `NG`) | [`schemes/UG/UG_seedbased.scheme`](schemes/UG/UG_seedbased.scheme), [`UG_expanded.scheme`](schemes/UG/UG_expanded.scheme) |
| §5.4 (UniversalCombiner with two KEMs) | [`schemes/UK/UK_seedbased.scheme`](schemes/UK/UK_seedbased.scheme), [`UK_expanded.scheme`](schemes/UK/UK_expanded.scheme) |
| §5.5 (C2PRICombiner with `NG`) | [`schemes/CG/CG_seedbased.scheme`](schemes/CG/CG_seedbased.scheme), [`CG_expanded.scheme`](schemes/CG/CG_expanded.scheme) |
| §5.6 (C2PRICombiner with two KEMs) | [`schemes/CK/CK_seedbased.scheme`](schemes/CK/CK_seedbased.scheme), [`CK_expanded.scheme`](schemes/CK/CK_expanded.scheme) |
| §6.2.1 (IND-CCA, complementary branches) | [`proofs/{UG,UK,CG,CK}/*_INDCCA_{PQ,T}.proof`](proofs/) |
| §6.4.1 (Binding) | [`proofs/{UG,UK,CG,CK}/*_LEAK_BIND_K_{CT,PK}.proof`](proofs/), [`proofs/{CG,CK}/*_HON_BIND_K_{CT,PK}.proof`](proofs/) |
| §6.4.2 (KDF security requirements) | [`games/KDF/`](games/KDF/) |

## Assumption table

The "primitive" column names the underlying primitive an assumption is
made about; the "game" column names the FrogLang game encoding the
assumption.

| Assumption | Primitive | Game | Used by |
|---|---|---|---|
| KEM correctness | `KEM` | [`Correctness`](games/KEM/Correctness.game) | Correctness proofs; IND-CCA via Decaps-rewrite hops |
| KEM IND-CCA | `KEM` | [`INDCCA`](games/KEM/INDCCA.game) / [`INDCCA_ROM`](games/KEM/INDCCA_ROM.game) | All `*_INDCCA_*` proofs |
| KEM C2PRI (ciphertext-to-plaintext rejection-immunity) | `KEM` (the PQ component) | [`C2PRI`](games/KEM/C2PRI.game) | `CK_*_INDCCA_T`, `CG_*_INDCCA_T`, expanded-form `{CG,CK}_LEAK_BIND_*` |
| KEM `KeyGenEquiv` | `KEM` | [`KeyGenEquiv`](games/KEM/KeyGenEquiv.game) | Bridging seed-form ↔ expanded-form (treated as a free fact for spec-compliant KEMs; see [Deviation 8](#deviation-8)) |
| KEM LEAK-BIND-K-{CT,PK} | `KEM` (the PQ component) | [`LEAK_BIND_K_CT`](games/KEM/Binding/LEAK_BIND_K_CT.game) / [`LEAK_BIND_K_PK`](games/KEM/Binding/LEAK_BIND_K_PK.game) (plus ROM variants) | All `{CG,CK}_*_LEAK_BIND_K_*` |
| PRG security | `PRG` | [`PRGSec`](games/PRG/PRGSec.game) | All seed-form proofs (used together with `KeyGenEquiv` to bridge seed and expanded forms) |
| KDF collision-resistance | `KDF` | [`KDFCollisionResistance`](games/KDF/KDFCollisionResistance.game) | All `*_LEAK_BIND_K_*` and `*_HON_BIND_K_*` |
| KDF first-key PRF | `KDF` | [`KDFFirstKeyPRF`](games/KDF/KDFFirstKeyPRF.game) | `{UG,UK,CG,CK}_*_INDCCA_PQ` (UG/CG cite single-key form; UK/CK cite split-key form) |
| KDF second-key PRF | `KDF` | [`KDFSecondKeyPRF`](games/KDF/KDFSecondKeyPRF.game) | `{UK,CK}_*_INDCCA_T` |
| KDF PRF security (single key) | `KDF` | [`KDFPRFSec`](games/KDF/KDFPRFSec.game) | UG IND-CCA branches |
| Nominal-group correctness | `NominalGroup` | [`NGCorrectness`](games/Group/NGCorrectness.game) | UG / CG correctness |
| Random-scalar distribution | `NominalGroup` | [`RandomScalarDist`](games/Group/RandomScalarDist.game) | UG / CG IND-CCA-T (ROM) |
| `SDH_SS` (shared-secret-keyed SDH variant) | `NominalGroup` | [`SDH_SS`](games/Group/SDH_SS.game) | `{UG,CG}_*_INDCCA_T` (ROM) — see [Deviation 10](#deviation-10) |
| `LazyROTwoViews*` (statistical helpers) | — | [`games/ROM/`](games/ROM/) | UG / CG IND-CCA-T (ROM hops) |
| `LazyROTwoSeeded` / `CGLazyROTwoSeeded` (statistical helpers) | — | [`games/ROM/`](games/ROM/) | Seed-form `{CG,CK}_*_LEAK_BIND_K_*` ([Deviation 7](#deviation-7)) |

## Deviations from the draft

1. **Quantum attacker.** Not modelled (see caveat above). ProofFrog
   makes no distinction between classical and quantum adversaries, so
   each proof is stated once. For our **standard-model** results, the
   same reduction also yields security against quantum adversaries
   provided every assumption it relies on (notably IND-CCA of `KEM_PQ`)
   holds against quantum adversaries; this re-interpretation is not
   separately mechanised. Our **ROM** results (the UG / CG T-branch
   IND-CCA proofs and the seeded-form CG / CK LEAK-BIND proofs of
   [Deviation 7](#deviation-7)) do **not** automatically lift to the QROM, since
   classical-RO reductions can fail against quantum adversaries that
   query the oracle in superposition. A QROM analysis would require
   separate proof effort outside ProofFrog.
2. **Two complementary branches.** All four frameworks have both
   complementary IND-CCA proofs. UG and CG traditional (T) branches (SDH) are in the
   ROM; all other IND-CCA proofs and all binding proofs (other than the
   seed-form CG/CK LEAK-BIND of [Deviation 7](#deviation-7)) are standard model.
3. **KDF model granularity.** The draft permits any RO-indifferentiable
   KDF; our standard-model IND-CCA proofs instead use weaker
   PRF-style assumptions on the KDF, treating the relevant component's
   shared secret as the PRF key: `KDFFirstKeyPRF` (the PQ shared secret
   `ss_PQ` is the key) for the PQ-branch IND-CCA proofs, and
   `KDFSecondKeyPRF` (the traditional shared secret `ss_T` is the key)
   for the UK and CK T-branch IND-CCA proofs. All binding proofs use
   only `KDFCollisionResistance`. These are instances of the
   alternative "PRF assumption" of draft §6.2.1.
4. **Seed / label byte layouts** are abstracted: `Label` is a primitive
   wrapper, and encoding methods (`KEM.Encode*`, `NG.Encode`,
   `NG.ElementToSharedSecret`) are declared with appropriate
   `injective` / `deterministic` modifiers but their byte-level layouts
   are left to the specification.
5. **Decapsulation key representation.** Draft §5.2 specifies the
   decapsulation key as the seed used to derive the component
   keypairs; `Decaps` is then defined to re-run `expandDecapsKey*(seed)`
   on every call to recover the underlying component decapsulation
   keys. Our `*_seedbased.scheme` files take this as the primary
   definition: `DecapsKey = BitString<G.lambda>` and every `Decaps`
   call expands the seed afresh. The draft permits, as an
   implementation cache, an "expanded" form in which the decapsulation
   key is the already-expanded keypair tuple
   `[K_PQ.DK, (K_T.DK, K_T.EK) | (NG scalar, NG element)]` and the
   expansion is not re-run; this is what our `*_expanded.scheme`
   files capture.

   The two representations are interchangeable for properties in which
   the seed is *hidden from the adversary* (correctness, IND-CCA,
   HON-BIND): in those games every seed-form proof opens with `PRGSec`
   (replacing `split(G(seed))` with fresh independent component seeds)
   followed by `KeyGenEquiv` applied once per component KEM (replacing
   `DeriveKeyPair(fresh seed)` with `KeyGen()`), after which the proof
   body operates on the expanded form. They are **not** interchangeable
   when the seed is *exposed* to the adversary, as in LEAK-BIND, where
   the adversary chooses the decapsulation key — `PRGSec` cannot be
   applied because its seed is no longer secret. This is the
   underlying reason that std-model LEAK-BIND for CG/CK is mechanised
   only against the `*_expanded.scheme` variant, with seed-form CG/CK
   LEAK-BIND requiring the PRG-as-RO construction of [Deviation 7](#deviation-7);
   see [Deviation 6](#deviation-6).

   Carrying the seed-form faithfully also adds engine burden — the
   seed-expansion appears inside every `Decaps` call and the
   canonicalizer must see it as constant across calls — but it is the
   configuration the draft actually defines, so we treat it as the
   primary statement of every property where it is mechanisable.
6. **Expanded-form scheme variant for CG/CK LEAK-BIND.** The
   `*_expanded.scheme` variants are used to obtain the standard-model
   LEAK-BIND result. We have not been able to mechanise seed-form
   CG/CK LEAK-BIND in the standard model under standard
   PRGSec / KGE / KDF-CR / KEM_PQ-binding assumptions: with the seed
   exposed to the adversary, `PRGSec` cannot be applied to convert the
   joint distribution of `(dk_PQ_0, dk_PQ_1)` into the form needed by
   the `KEM_PQ.LEAK-BIND` reduction, and we did not find an
   alternative route. The seed-form result is recovered under the
   PRG-as-RO construction of [Deviation 7](#deviation-7).
7. **Seed-form CG/CK LEAK-BIND uses a ROM-style construction for `G`.**
   The four `{CG,CK}_seedbased_LEAK_BIND_K_{CT,PK}` proofs depart from
   the standard model in three ways, all confined to those four
   proofs:

   1. *The seed-expansion PRG `G` is modelled as a random oracle.*
      Concretely, we replace `G` with a `Function<...>` sampled at
      the start of the game, exposed to the reduction via the wrapper
      schemes
      [`CKRandomOraclePRG`](schemes/CK/CKRandomOraclePRG.scheme) and
      [`CGRandomOraclePRG`](schemes/CG/CGRandomOraclePRG.scheme). This
      lets the reduction *program* `G`'s output on the challenge seeds.
      The component KEM's `KeyGen` / `DeriveKeyPair` is **not**
      modelled as a random oracle — only `G` is.
   2. *The K_PQ binding assumption is stated in seed form.* The
      reduction reduces hybrid-KEM binding to binding of `KEM_PQ`,
      but in a form where the `KEM_PQ` decapsulation key is itself
      the seed passed to `DeriveKeyPair`, exposed via
      [`SeededKEMWrapper`](schemes/Helpers/SeededKEMWrapper.scheme).
      For KEMs whose `KeyGen` is defined as `DeriveKeyPair(uniform seed)`
      — including ML-KEM (FIPS 203), HQC, and the FO-style KEMs
      targeted by the draft — this is the natural way to state binding
      and matches what the draft assumes. It looks formally stronger
      than expanded-form binding only because ProofFrog cannot express
      "given the expanded key, the seed is hard to recover".
   3. *A statistical helper game closes the gap between the bare
      programmed-RO view and the form the reduction needs.*
      [`LazyROTwoSeeded`](games/ROM/LazyROTwoSeeded.game) and
      [`CGLazyROTwoSeeded`](games/ROM/CGLazyROTwoSeeded.game)
      bound that gap by `2^{-lambda}` — they are statistical, not
      cryptographic, assumptions, in the same spirit as the
      `LazyROTwoViews*` helpers used by the UG/CG IND-CCA-T proofs.
8. **`KeyGenEquiv` as a free fact.** The
   [`KeyGenEquiv`](games/KEM/KeyGenEquiv.game) game asserts that
   `KeyGen()` is distributionally equivalent to
   `[s <- BitString<Nseed>; DeriveKeyPair(s)]`. We treat this as a
   definitional equality, not as an additional cryptographic
   assumption, because for KEMs whose `KeyGen` is *defined* as
   `DeriveKeyPair(uniform seed)` — including ML-KEM (FIPS 203), HQC,
   and the FO-style KEMs targeted by the draft — the two sides are
   literally the same algorithm. ProofFrog requires it to be stated
   explicitly only because `KEM.primitive` declares `KeyGen` and
   `DeriveKeyPair` as independent methods with no inter-method
   relationship; a real-world instantiation would discharge it by
   inspection of the spec. Same caveat as [Deviation 7](#deviation-7).ii: this does
   not apply to KEMs whose `KeyGen` deviates from the
   `DeriveKeyPair(uniform seed)` template.
9. **`KEM_C2PRI(KEM_PQ)` as a named assumption.** The CK / CG
    T-branch IND-CCA proofs and the expanded-form CG/CK LEAK-BIND
    proofs reduce binding/CCA security of the hybrid to properties of
    the traditional component (IND-CCA of `KEM_T` or SDH on `NG`),
    but still require `KEM_PQ` to behave well enough that adversarial
    ciphertexts cannot induce shared-secret collisions on the PQ side.
    We capture this with `KEM_C2PRI(KEM_PQ)`
    (ciphertext-to-plaintext-rejection-immunity), a property strictly
    weaker than IND-CCA. The draft alludes to such a residual
    requirement on `KEM_PQ` in §6.2.1 but does not name a specific
    assumption; we pin it down to C2PRI, which is a known assumption
    from the literature (StarHunters; X-Wing; the HPKE and Kyber binding
    analyses). Listed as a deviation only in the sense that the
    specific assumption name is ours, not the draft's.
10. **`SDH_SS(NG)` rather than standard SDH.** Variant of Strong DH in
    which the adversary's goal is to produce the *shared-secret*
    representation `NG.ElementToSharedSecret(g^{ab})` (a `BitString<Nss>`)
    rather than the group element `g^{ab}` itself, with a decision
    oracle on that same representation. Independent of standard SDH
    because `ElementToSharedSecret` is non-injective per draft §4.2
    (X-coordinate instantiation is 2-to-1), so winning standard SDH
    does not directly yield an `SDH_SS` win and vice versa. Listed as a
    sibling of SDH in the assumption table.
11. **Non-injective `NG.ElementToSharedSecret`.**
    [`NominalGroup.primitive`](primitives/NominalGroup.primitive)
    declares `ElementToSharedSecret` *without* the `injective`
    modifier, faithful to draft §4.2 (which does not mandate
    injectivity, and for which the X-coordinate-only instantiation is
    in fact 2-to-1). This blocks engine simplifications that would
    treat the output as identifying its input — see [Deviation 10](#deviation-10) for
    the consequence on the SDH-style assumption used by the UG/CG
    T-branches.
12. **Implicit rejection.** Restated here for completeness; see the
    top-of-document modelling caveat for full text. Our binding
    games do not include the CDM24 Fig. 5 `bot`-guard, which is sound
    for implicitly-rejecting KEMs (FO-style, ML-KEM) but means the
    results do not transfer to explicitly-rejecting KEMs without
    extending [`KEM.primitive`](primitives/KEM.primitive).
13. **`Label` primitive wrapper.** The draft passes the
    domain-separation label as a raw byte string. FrogLang scheme
    parameters cannot be raw `BitString`s — they must be primitive
    instances, `Int`s, or typed `Function<...>`s — so we wrap the
    label in a [`Label`](primitives/Label.primitive) primitive
    exposing one `deterministic BitString<Nlabel> get();` method.
    Semantically equivalent to passing the label byte-string directly;
    only the surface-level packaging differs.

## Verification

```bash
# Parse + type-check.
python -m proof_frog parse  examples/applications/cfrg-hybrid-kems/**/*.primitive
python -m proof_frog parse  examples/applications/cfrg-hybrid-kems/**/*.game
python -m proof_frog check  examples/applications/cfrg-hybrid-kems/**/*.scheme

# Verify each proof.
for f in examples/applications/cfrg-hybrid-kems/proofs/**/*.proof; do
    python -m proof_frog prove "$f" || echo "FAIL: $f"
done

# Integration suite.
pytest tests/integration/test_proofs.py -k cfrg_hybrid_kems
```

## Out of scope

- Concrete instantiations (ML-KEM, X25519, etc.). All proofs are
  generic over the component KEM / nominal group.
- Explicitly-rejecting KEMs (see modelling caveat).
- Quantum-attacker reasoning (see [Deviation 1](#deviation-1)).
