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
57 proofs of correctness, IND-CCA, LEAK-BIND-K-{CT,PK}, and
HON-BIND-K-{CT,PK}.

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
| [`primitives/`](primitives/) | `KEM`, `NominalGroup`, `KDF`, `PRG`, `Label`, `HashInputPacking` |
| [`games/KEM/`](games/KEM/) | `INDCCA`, `INDCCA_ROM`, `Correctness`, `CorrectnessWithDK`, `KeyGenEquiv`, `C2PRI`, plus [`Binding/`](games/KEM/Binding/) and its ROM variants |
| [`games/Group/`](games/Group/) | `SDH`, `SDH_SS`, `NGCorrectness`, `RandomScalarDist` |
| [`games/KDF/`](games/KDF/) | `KDFCollisionResistance`, `KDFFirstKeyPRF`, `KDFSecondKeyPRF`, `KDFPRFSec` |
| [`games/PRG/`](games/PRG/) | `PRGSec` |
| [`games/ROM/`](games/ROM/) | Statistical helper games: `LazyROTwoViewsExcluded[Programmed]`, `LazyRO{One,Two}Seeded`, `CGLazyRO{One,Two}Seeded`. All six carry an LLM-written EasyCrypt proof of their declared bound (`*.ec` alongside). |
| [`schemes/{UG,UK,CG,CK}/`](schemes/) | `*_seedbased.scheme`, `*_expanded.scheme`; RO-flavoured PRG/KDF wrapper schemes |
| [`schemes/Helpers/`](schemes/Helpers/) | `SeededKEMWrapper.scheme` |
| [`proofs/{UG,UK,CG,CK}/`](proofs/) | All correctness, IND-CCA, and binding proofs |
| [`proofs/Generic/`](proofs/Generic/) | `LEAK_implies_HON_BIND_K_{CT,PK}` |

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

- Concrete instantiations (ML-KEM, X25519, P-256, and so on). All proofs are
  generic over the component KEM and nominal group.
- Explicitly rejecting KEMs.
- Quantum-attacker reasoning; ROM results do not lift to the QROM.

See [Section 5 of the report](REPORT-CFRG-20260722.md#5-scope-and-caveats) for the
full statement of what these proofs do and do not establish.
