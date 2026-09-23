# ProofFrog formalization of draft-irtf-cfrg-hybrid-kems

FrogLang models and machine-checked ProofFrog proofs of the four hybrid
KEM frameworks specified in:

> CFRG, *Hybrid PQ/T Key Encapsulation Mechanisms*,
> [draft-irtf-cfrg-hybrid-kems](https://datatracker.ietf.org/doc/draft-irtf-cfrg-hybrid-kems/).
> Models were built against **-10**; see the report for the differences from -12.

The four frameworks (draft Sections 5.3 to 5.6) each combine a post-quantum KEM
(`KEM_PQ`) with a traditional component, either another KEM (`KEM_T`) or a
nominal group (`NG`, draft Section 4), via a key-derivation function (`KDF`).
This directory contains scheme definitions for all four, together with
65 proofs of correctness, IND-CCA, LEAK-BIND-K-{CT,PK}, and
HON-BIND-K-{CT,PK}, and one proof about ML-KEM itself, which discharges
the only assumption those proofs make about a concrete component.

> This README describes what the artifact contains and how to run it.
> The results, the assumptions they rest on, the modelling choices and
> their limits, and our comments to the research group are in
> **[REPORT-CFRG-20260722.md](REPORT-CFRG-20260722.md)**; the per-proof
> assumption counts are in its companion
> **[BOUNDS-CFRG-20260722.md](BOUNDS-CFRG-20260722.md)**. Read the report
> before citing anything from this directory, in particular its Section 5
> (scope and caveats), which characterizes what these proofs establish.

## Directory layout

| Path | Contents |
|------|----------|
| [`primitives/`](primitives/) | `KEM`, `NominalGroup`, `KDF`, `PRG`, `Label`, `HashInputPacking`, plus `DetPKE` and `Hash` for the ML-KEM instantiation |
| [`games/KEM/`](games/KEM/) | `INDCCA`, `INDCCA_ROM`, `Correctness`, `CorrectnessWithDK`, `KeyGenEquiv`, `KEMKeyCollision`, `C2PRI`, plus [`Binding/`](games/KEM/Binding/) (`{LEAK,HON}_BIND_K_*`, their ROM variants, and the seed-keyed malicious `MALSEED_BIND_K_CT_SAMEKEY`) |
| [`games/Group/`](games/Group/) | `SDH`, `SDH_SS`, `NGCorrectness`, `RandomScalarDist`, `NGKeyCollision` |
| [`games/KDF/`](games/KDF/) | `KDFCollisionResistance`, `KDFFirstKeyPRF`, `KDFSecondKeyPRF`, `KDFPRFSec` |
| [`games/PRG/`](games/PRG/) | `PRGSec` |
| [`games/Hash/`](games/Hash/) | `HashCollisionResistance`, `TruncatedCollisionResistance`, `CrossCollisionResistance`: the three hash assumptions the ML-KEM binding proof rests on |
| [`games/Helpers/`](games/Helpers/) | Declared-zero-advantage identities used by the ML-KEM proof: `MLKEMDecapsCaseSplit` (the binding predicate rewritten as a case analysis) and `FOReEncryptionCongruence` (distinct ciphertexts that both re-encrypt come from distinct messages) |
| [`games/ROM/`](games/ROM/) | Statistical helper games: `LazyROTwoViewsExcluded[Programmed]`, `LazyRO{One,Two}Seeded`, `CGLazyRO{One,Two}Seeded`. All six carry an LLM-written EasyCrypt proof of their declared bound (`*.ec` alongside). |
| [`games/Seeded/`](games/Seeded/) | Key-generation event games for the standard-model LEAK-BIND proofs of seeded CG and CK: `{CG,CK}SeededTKeyCollision` (seeds exposed; the assumption the main proofs use) and `{CG,CK}SeededTKeyCollisionEvent` (seeds hidden; bounded in ProofFrog by `proofs/{CG,CK}/*_TKeyCollisionEvent.proof` from `PRGSec` plus the component's key-collision probability). |
| [`schemes/{UG,UK,CG,CK}/`](schemes/) | `*_seedbased.scheme`, `*_expanded.scheme`; RO-flavoured PRG/KDF wrapper schemes |
| [`schemes/MLKEM/`](schemes/MLKEM/) | `MLKEM.scheme`: FIPS 203 as a seeded KEM, generic over the K-PKE layer |
| [`schemes/Helpers/`](schemes/Helpers/) | `SeededKEMWrapper.scheme` |
| [`proofs/{UG,UK,CG,CK}/`](proofs/) | All correctness, IND-CCA, and binding proofs |
| [`proofs/Generic/`](proofs/Generic/) | `LEAK_implies_HON_BIND_K_{CT,PK}` |
| [`proofs/MLKEM/`](proofs/MLKEM/) | `MLKEM_MALSEED_BIND_K_CT_SAMEKEY.proof`: discharges, for ML-KEM, the PQ assumption of the seeded `_std` SAMEKEY proofs |

## Naming conventions

Proof filenames are `<framework>_<form>_<property>.proof`.

- **Framework.** `UG`, `UK`, `CG`, `CK`. The first letter is the combiner
  (`U` = UniversalCombiner, draft Sections 5.3 and 5.4; `C` = C2PRICombiner,
  Sections 5.5 and 5.6); the second is the traditional component
  (`G` = nominal group, `K` = KEM).
- **Form.** `seedbased` (draft -12 Section 5.2's primary definition: `dk` is
  the seed and `Decaps` re-runs `expandDecapsKey*` on every call) or
  `expanded` (`dk = (dk_PQ, ek_PQ, dk_T, ek_T)`, the alternative that the
  same section permits).
- **Property.** `Correctness`, `INDCCA_{PQ,T}` for the two complementary
  branches, and `{LEAK,HON}_BIND_K_{PK,CT_DIFFKEY,CT_SAMEKEY}`.
- **Suffix `_std`.** For seeded CG and CK, the three `LEAK_BIND_K_*`
  properties exist twice: the original proofs model the seed-expansion
  PRG as a programmable random oracle and reduce to the PQ KEM's LEAK
  binding; the `_std` variants are standard-model proofs. For
  `LEAK_BIND_K_PK` and `LEAK_BIND_K_CT_DIFFKEY` they follow the route of
  StarFighters Theorem 28 (ePrint 2025/1397): KDF collision resistance plus
  the probability that the two traditional public keys collide, with no
  assumption on the PQ KEM; the companion `*_TKeyCollisionEvent.proof`
  files bound that probability. For `LEAK_BIND_K_CT_SAMEKEY` no such case
  split exists (the C2PRI KDF input has no `ct_PQ` slot, so a single-key
  break is a same-key ciphertext-binding break of the PQ KEM), and the
  `_std` proof instead assumes the *seed-keyed malicious* notion
  `MALSEED_BIND_K_CT_SAMEKEY` of the PQ KEM (the adversary chooses the seed
  the PQ key pair is derived from; between CDM24's LEAK and MAL, implied by
  MAL-BIND-K-CT): a reduction can then generate the hybrid seed itself and
  submit the PQ seed it expanded from it, whereas the LEAK notion would
  require embedding a challenge key pair into a seed, which only a
  programmable random oracle allows. Keying the notion by the seed matches
  the draft's `expandDecapsKey`, which always derives `dk_PQ` from
  `seed_PQ`, and rules out the malformed keys on which the known
  MAL-BIND attacks on ML-KEM rely (Schmieg, ePrint 2024/523). For ML-KEM
  that assumption is not left standing: it is discharged by
  [`proofs/MLKEM/MLKEM_MALSEED_BIND_K_CT_SAMEKEY.proof`](proofs/MLKEM/MLKEM_MALSEED_BIND_K_CT_SAMEKEY.proof),
  and the game file's header records what is known for the notion.

The one concrete instantiation in this directory is ML-KEM, named for the
scheme rather than by a framework letter:
[`schemes/MLKEM/MLKEM.scheme`](schemes/MLKEM/MLKEM.scheme) is FIPS 203's
Fujisaki-Okamoto transform over an abstract deterministic PKE
([`primitives/DetPKE.primitive`](primitives/DetPKE.primitive)), with
SHA3-256, SHA3-512 and SHAKE256 modelled as standard-model
[`Hash`](primitives/Hash.primitive) primitives, and
[`proofs/MLKEM/MLKEM_MALSEED_BIND_K_CT_SAMEKEY.proof`](proofs/MLKEM/MLKEM_MALSEED_BIND_K_CT_SAMEKEY.proof)
proves it seed-keyed malicious single-key ciphertext binding. No lattice
structure is modelled and no property of K-PKE is assumed; the argument is
entirely about the FO transform's hashing, so it establishes exactly the
assumption the seeded CG and CK `_std` SAMEKEY proofs make about
`KEM_PQ`, and nothing about ML-KEM's IND-CCA security.

`K-CT` binding is split across two files. Figure 5 of
[CDM24](REPORT-CFRG-20260722.md#ref-cdm24), the source of the binding notions,
gives an `X-BIND-K-CT` that lets the adversary choose a bit selecting
between two scenarios: two
independently generated receiver keypairs (`DIFFKEY`) or a single keypair
with a re-encapsulation collision (`SAMEKEY`). A KEM is K-CT-binding iff
it withstands both, so each is mechanized as a straight-line game and both
are proved. Draft -12 Section 6.4.2 describes the same case distinction.

## Mapping from draft sections to files

| Draft section | File |
|---|---|
| Section 4.1 (KEMs) | [`primitives/KEM.primitive`](primitives/KEM.primitive) |
| Section 4.2 (Nominal groups) | [`primitives/NominalGroup.primitive`](primitives/NominalGroup.primitive) |
| Section 5.2 (Seed-form decapsulation key) | All `*_seedbased.scheme` files |
| Section 5.2 (Expanded decapsulation key) | All `*_expanded.scheme` files |
| Section 5.3 (UniversalCombiner with `NG`) | [`schemes/UG/`](schemes/UG/) |
| Section 5.4 (UniversalCombiner with two KEMs) | [`schemes/UK/`](schemes/UK/) |
| Section 5.5 (C2PRICombiner with `NG`) | [`schemes/CG/`](schemes/CG/) |
| Section 5.6 (C2PRICombiner with two KEMs) | [`schemes/CK/`](schemes/CK/) |
| Section 6.1.2 (C2PRI) | [`games/KEM/C2PRI.game`](games/KEM/C2PRI.game) |
| Section 6.1.3 (Strong Diffie-Hellman) | [`games/Group/SDH.game`](games/Group/SDH.game); our proofs use the variant [`games/Group/SDH_SS.game`](games/Group/SDH_SS.game) instead, as discussed in [Finding F2 of the report](REPORT-CFRG-20260722.md#f2-the-traditional-branches-of-ug-and-cg-depend-on-a-variant-of-sdh-over-shared-secret-encodings-not-group-elements) |
| Section 6.1.4 (Binding properties) | [`games/KEM/Binding/`](games/KEM/Binding/) |
| Section 6.1.6 (PRG requirements) | [`games/PRG/PRGSec.game`](games/PRG/PRGSec.game) |
| Sections 6.2.1 and 6.4.1 (IND-CCA) | [`proofs/*/[A-Z]*_INDCCA_{PQ,T}.proof`](proofs/) |
| Sections 6.2.2 and 6.4.2 (Binding) | [`proofs/*/[A-Z]*_BIND_*.proof`](proofs/) |

## Verifying

From the repository root:

```bash
D=examples/applications/cfrg-hybrid-kems

# Parse the primitives and games.
for f in $D/primitives/*.primitive $D/games/*/*.game $D/games/*/*/*.game; do
    python -m proof_frog parse "$f" || echo "FAIL: $f"
done

# Type-check the schemes.
for f in $D/schemes/*/*.scheme; do
    python -m proof_frog check "$f" || echo "FAIL: $f"
done

# Verify every proof.
for f in $D/proofs/*/*.proof; do
    python -m proof_frog prove "$f" || echo "FAIL: $f"
done

# Or via the integration suite.
pytest tests/integration/test_proofs.py -k cfrg-hybrid-kems
```

Each proof declares a `bound:` clause stating the concrete advantage bound
it establishes; `prove` checks the claim against the bound it synthesizes
from the hop sequence.

To inspect a single proof:

```bash
python -m proof_frog prove   <file>.proof   # verify, print the hop table and bound
python -m proof_frog describe <file>.game   # human-readable game description
```

## EasyCrypt re-checking

As an independent check, proofs are also exported to EasyCrypt, where 28 of
the 57 are currently accepted. That coverage and its caveats, including that
the exported EasyCrypt models and proofs have not been reviewed by an
EasyCrypt expert, are in
[Section 3.5 of the report](REPORT-CFRG-20260722.md#35-exporting-from-prooffrog-to-easycrypt).

## Out of scope

- Concrete instantiations (X25519, P-256, and so on): every hybrid proof is
  generic over the component KEM and nominal group. The one exception is
  ML-KEM, and only for one property -- `MALSEED-BIND-K-CT-SAMEKEY`, the
  assumption the seeded `_std` SAMEKEY proofs make about `KEM_PQ`. Nothing
  here bears on ML-KEM's IND-CCA security or its lattice layer.
- Explicitly rejecting KEMs.
- Quantum-attacker reasoning; ROM results do not lift to the QROM.

See [Section 5 of the report](REPORT-CFRG-20260722.md#5-scope-and-caveats) for the
full statement of what these proofs do and do not establish.
