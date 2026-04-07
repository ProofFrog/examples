# Constructions from The Joy of Cryptography (MIT Press Edition)

This directory ([examples/joy](https://github.com/ProofFrog/examples/tree/main/joy)) contains ProofFrog versions of constructions from Chapters 1 and 2 of [The Joy of Cryptography](https://joyofcryptography.com/) by Mike Rosulek. Those aiming to learn how to do provable security proofs using ProofFrog may find it helpful to read those two chapters of Joy of Cryptography in parallel with the corresponding ProofFrog files.

| Book reference | Description | ProofFrog File |
|---|---|---|
| [**Chapter 1**](https://joyofcryptography.com/otp/) | [One-Time Pad and the Provable Security Mindset](https://joyofcryptography.com/otp/) | |
| [Construction 1.2.1](https://joyofcryptography.com/otp/#sec.otp:~:text=Construction%201%2E2%2E1) | One-Time Pad | [examples/joy/Schemes/SymEnc/OTP.scheme](Schemes/SymEnc/OTP.scheme) |
| [Claim 1.2.3](https://joyofcryptography.com/otp/#sec.otp:~:text=Claim%201%2E2%2E3) | OTP correctness | [examples/joy/Games/SymEnc/Correctness.game](Games/SymEnc/Correctness.game), [examples/joy/Proofs/Ch1/OTPCorrectness.proof](Proofs/Ch1/OTPCorrectness.proof) |
| [**Chapter 2**](https://joyofcryptography.com/provsec/) | [Rudiments of Provable Security](https://joyofcryptography.com/provsec/) | |
| [Definition 2.5.1](https://joyofcryptography.com/provsec/#sec.abstract-defs:~:text=Definition%202%2E5%2E1) | Symmetric-key encryption | [examples/joy/Primitives/SymEnc.primitive](Primitives/SymEnc.primitive) |
| [Definition 2.5.3](https://joyofcryptography.com/provsec/#sec.abstract-defs:~:text=Definition%202%2E5%2E3) | One-time secrecy (real-or-random) | [examples/joy/Games/SymEnc/OneTimeSecrecy.game](Games/SymEnc/OneTimeSecrecy.game) |
| [Example 2.5.4](https://joyofcryptography.com/provsec/#sec.abstract-defs:~:text=Example%202%2E5%2E4) | OTP has one-time secrecy | [examples/joy/Proofs/Ch2/OTPSecure.proof](Proofs/Ch2/OTPSecure.proof) |
| [Construction 2.6.1](https://joyofcryptography.com/provsec/#sec.modular:~:text=Construction%202%2E6%2E1) | Chained encryption | [examples/joy/Schemes/SymEnc/ChainedEncryption.scheme](Schemes/SymEnc/ChainedEncryption.scheme) |
| [Claim 2.6.2](https://joyofcryptography.com/provsec/#sec.modular:~:text=Claim%202%2E6%2E2) | Chained encryption has one-time secrecy | [examples/joy/Proofs/Ch2/ChainedEncryptionSecure.proof](Proofs/Ch2/ChainedEncryptionSecure.proof) |
| [Definition 2.7.1](https://joyofcryptography.com/provsec/#sec.left-right:~:text=Definition%202%2E7%2E1) | One-time secrecy (left-or-right) | [examples/joy/Games/SymEnc/OneTimeSecrecyLR.game](Games/SymEnc/OneTimeSecrecyLR.game) |
| – | OTP has one-time secrecy (left-or-right) | [examples/joy/Proofs/Ch2/OTPSecureLR.proof](Proofs/Ch2/OTPSecureLR.proof) |

## Exercises

The following exercises from Joy of Cryptography are doable in ProofFrog. Solutions are not publicly available, but instructors can contact Douglas Stebila to get a copy.

| Book reference | Description |
|---|---|
| [**Chapter 2**](https://joyofcryptography.com/provsec/#sec.left-right:~:text=Exercises,-Show) | |
| [Exercise 2.6](https://joyofcryptography.com/provsec/#sec.left-right:~:text=Prove%20that%20the%20following%20two%20libraries%20are%20interchangeable%2C%20for%20all) | Sampling difference of two uniform `ModInt<q>` values is uniform |
| [Exercise 2.7](https://joyofcryptography.com/provsec/#sec.left-right:~:text=R%E2%80%BE-,R,R,-%E2%80%94that) | Bitwise complement of a uniform bitstring is uniform |
| [Exercise 2.8](https://joyofcryptography.com/provsec/#sec.left-right:~:text=R%2E-,Prove%20that%20the%20following%20two%20libraries%20are%20interchangeable%3A) | `A \|\| (A XOR B)` is interchangeable with a uniform `2n`-bit string |
| [Exercise 2.9b](https://joyofcryptography.com/provsec/#sec.left-right:~:text=Below%20are%20two%20pairs%20of%20libraries%2E%20One%20pair%20is%20interchangeable%2C%20one%20is%20not%2E%20Give%20a%20proof%20and%20a%20distinguishing%20attack) | `(A XOR B) \|\| (B XOR C)` is interchangeable with a uniform `2n`-bit string |
| [Exercise 2.17](https://joyofcryptography.com/provsec/#sec.left-right:~:text=Show%20that%20construction%202%2E6%2E1%20satisfies%20the%20correctness%20property) | Chained encryption is correct |
| [Exercise 2.21](https://joyofcryptography.com/provsec/#sec.left-right:~:text=it%20is%20safe%20to%20encrypt%20the%20same%20plaintext%20twice%2C%20under%20two%20independent%20keys) | Encrypt-twice has one-time secrecy |
| [Exercise 2.22](https://joyofcryptography.com/provsec/#sec.left-right:~:text=it%20is%20safe%20to%20encrypt%20a%20long%20plaintext%20by%20separately%20encrypting%20its%20two%20halves%20%28under%20independent%20keys%29%2E) | Encrypt-halves has one-time secrecy |
| [Exercise 2.23](https://joyofcryptography.com/provsec/#sec.left-right:~:text=it%20makes%20sense%20to%20treat%20a%20ciphertext%20also%20as%20a%20plaintext%20that%20can%20be%20encrypted) | Double encryption has one-time secrecy |
| [Exercise 2.24](https://joyofcryptography.com/provsec/#sec.left-right:~:text=scheme%2E-,Prove,OTS) | Real-or-random OTS implies left-or-right OTS |
| [Exercise 2.25b](https://joyofcryptography.com/provsec/#sec.left-right:~:text=does%2E-,Show,0,-does) | Append-zero scheme has left-or-right OTS |
| [Exercise 2.26b](https://joyofcryptography.com/provsec/#sec.left-right:~:text=2%2EEnc%28K%2CM%29-,%CE%A3,K%2CM%29%3A) | Double-ciphertext scheme has left-or-right OTS |
| [Exercise 2.27](https://joyofcryptography.com/provsec/#sec.left-right:~:text=does%2E-,Prove,secrecy) | Encrypt-then-ignore-input characterization of left-or-right OTS (both directions) |
| [Exercise 2.28](https://joyofcryptography.com/provsec/#notes) | Swap-ciphertext characterization of left-or-right OTS (both directions) |
