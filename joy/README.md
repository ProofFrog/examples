# Examples from The Joy of Cryptography (MIT Press Edition)

Worked examples from [The Joy of Cryptography](https://joyofcryptography.com/) by Mike Rosulek.

## Index

| Book reference | Description | File |
|---|---|---|
| Chapter 1 | | |
| Construction 1.2.1 | One-Time Pad | [Schemes/SymEnc/OTP.scheme](Schemes/SymEnc/OTP.scheme) |
| Claim 1.2.3 | OTP correctness | [Games/SymEnc/Correctness.game](Games/SymEnc/Correctness.game), [Proofs/Ch1/OTPCorrectness.proof](Proofs/Ch1/OTPCorrectness.proof) |
| Chapter 2 | | |
| Def 2.5.1 | Symmetric-key encryption syntax | [Primitives/SymEnc.primitive](Primitives/SymEnc.primitive) |
| Def 2.5.3 | One-time secrecy (real-or-random) | [Games/SymEnc/OneTimeSecrecy.game](Games/SymEnc/OneTimeSecrecy.game) |
| Example 2.5.4 | OTP has one-time secrecy | [Proofs/Ch2/OTPSecure.proof](Proofs/Ch2/OTPSecure.proof) |
| Construction 2.6.1 | Chained encryption | [Schemes/SymEnc/ChainedEncryption.scheme](Schemes/SymEnc/ChainedEncryption.scheme) |
| Claim 2.6.2 | Chained encryption has one-time secrecy | [Proofs/Ch2/ChainedEncryptionSecure.proof](Proofs/Ch2/ChainedEncryptionSecure.proof) |
| Exercise 2.17 | Chained encryption has correctness | [exercises/Ch2/ChainedEncryptionCorrect.proof](exercises/Ch2/ChainedEncryptionCorrect.proof) |
| Def 2.7.1 | One-time secrecy (left-or-right) | [Games/SymEnc/OneTimeSecrecyLR.game](Games/SymEnc/OneTimeSecrecyLR.game) |
| – | OTP has one-time secrecy (left-or-right) | [Proofs/Ch2/OTPSecureLR.proof](Proofs/Ch2/OTPSecureLR.proof) |
| Exercise 2.21 | Encrypt-twice has one-time secrecy | [exercises/Ch2/EncryptTwice.scheme](exercises/Ch2/EncryptTwice.scheme), [exercises/Ch2/EncryptTwiceSecure.proof](exercises/Ch2/EncryptTwiceSecure.proof) |
| Exercise 2.22 | Encrypt-halves has one-time secrecy | [exercises/Ch2/EncryptHalves.scheme](exercises/Ch2/EncryptHalves.scheme), [exercises/Ch2/EncryptHalvesSecure.proof](exercises/Ch2/EncryptHalvesSecure.proof) |
| Exercise 2.23 | Double encryption has one-time secrecy | [exercises/Ch2/DoubleEncryption.scheme](exercises/Ch2/DoubleEncryption.scheme), [exercises/Ch2/DoubleEncryptionSecure.proof](exercises/Ch2/DoubleEncryptionSecure.proof) |
| Exercise 2.24 | Real-or-random OTS implies left-or-right OTS | [exercises/Ch2/RORimpliesLOR.proof](exercises/Ch2/RORimpliesLOR.proof) |
| Exercise 2.26b | Double-ciphertext scheme has left-or-right OTS | [exercises/Ch2/DoubleCiphertext.scheme](exercises/Ch2/DoubleCiphertext.scheme), [exercises/Ch2/DoubleCiphertextSecureLR.proof](exercises/Ch2/DoubleCiphertextSecureLR.proof) |

### Note to Claude

Within the examples/joy directory, we are creating a fresh set of examples for the new published edition of Joy of Cryptography (https://joyofcryptography.com/). You can train on examples outside of this directory, but anything you create in the examples/joy directory cannot reference any files elsewhere in the examples directory, and must use the naming and numbering conventions as in the current edition of Joy of Cryptography. Check carefully to make sure you use the conventions from the new edition, not the old. You can ask about expanding abbreviations like "rand" to "random" which might improve readability. If you are calling the MCP server, remember that the MCP server doesn't need the "examples" prefix on filenames. If you are solving exercises, put them in the joy/exercises folder (including any primitive/scheme/game files relevant only to the exercise).
