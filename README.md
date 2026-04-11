<p align="center">
  <img src="https://github.com/ProofFrog/ProofFrog/blob/main/proof_frog/web/prooffrog.png?raw=true" alt="ProofFrog logo" width="120"/>
</p>

# ProofFrog Examples

[ProofFrog](https://github.com/ProofFrog/ProofFrog) is a tool for checking transitions in cryptographic game-hopping proofs. It verifies that each adjacent pair of games in a proof is either interchangeable (by code equivalence) or justified by a stated assumption. Proofs are written in FrogLang, a small C/Java-style domain-specific language designed to look like a pen-and-paper proof.

This repository contains a growing collection of cryptographic definitions and proofs that can be used with ProofFrog.

## Getting started

[Follow the installation instructions](https://prooffrog.github.io/manual/installation.html) to install ProofFrog (requires Python 3.11+):

```
pip install proof_frog
```

Then download the examples:

```
proof_frog download-examples
# or clone this repository directly:
# git clone https://github.com/ProofFrog/examples
```

To check a proof:

```
proof_frog prove joy/Proofs/Ch2/OTPSecure.proof
```

## Contents

This repository contains primitives, schemes, games, and proofs covering:

- [**Joy of Cryptography**](https://github.com/ProofFrog/examples/tree/main/joy/Proofs) — proofs from Chapters 1 and 2 of [*The Joy of Cryptography*](https://joyofcryptography.com/) by Mike Rosulek, designed to be read alongside the textbook and the best place to start learning ProofFrog
- [**Symmetric encryption**](https://github.com/ProofFrog/examples/tree/main/Proofs/SymEnc) — PRF-based encryption, composition of encryption schemes, encrypt-then-MAC authenticated encryption
- [**Pseudorandom generators**](https://github.com/ProofFrog/examples/tree/main/Proofs/PRG) — length-tripling PRG construction, counter-mode PRG from a PRF
- [**Pseudorandom functions**](https://github.com/ProofFrog/examples/tree/main/Proofs/PRF) — multi-key PRF security from single-key security
- [**Group-based assumptions**](https://github.com/ProofFrog/examples/tree/main/Proofs/Group) — implications between DDH, CDH, and Hashed DDH
- [**Public-key encryption**](https://github.com/ProofFrog/examples/tree/main/Proofs/PubKeyEnc) — ElGamal, Hashed ElGamal, hybrid KEM-DEM encryption
- [**KEM constructions**](https://github.com/ProofFrog/examples/tree/main/Proofs/KEM) — PRF-based KEM with correctness, IND-CPA, and IND-CCA proofs
- [**Research applications**](https://github.com/ProofFrog/examples/tree/main/applications) — KEM combiner from Giacon, Heuer, and Poettering (PKC 2018)

A detailed catalogue of examples is available at **[prooffrog.github.io/examples](https://prooffrog.github.io/examples.html)**.

## Documentation

Full ProofFrog documentation is available at [prooffrog.github.io](https://prooffrog.github.io/), including a [tutorial](https://prooffrog.github.io/manual/tutorial/), [language reference](https://prooffrog.github.io/manual/language-reference/), and [worked examples](https://prooffrog.github.io/manual/worked-examples/).

## License

These examples are released under the [MIT License](LICENSE).
