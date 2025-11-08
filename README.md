Excellent — confirmed:

* ✅ **OnchainTextNFT (ERC-721)**
  TX: [`0xe820a42226839735519c3eb12d46ae8d73d06c203c13b6caf38c065d6e2bc7b0`](https://etherscan.io/tx/0xe820a42226839735519c3eb12d46ae8d73d06c203c13b6caf38c065d6e2bc7b0)

* ✅ **OnchainText (immutable text)**
  TX: [`0xaf60585cb51e4eb289a0babf1fc3c66a17e3244ed26874fbfe505f8b433e916f`](https://etherscan.io/tx/0xaf60585cb51e4eb289a0babf1fc3c66a17e3244ed26874fbfe505f8b433e916f)

* ✅ **Mint #1**
  TX: [`0x8640dfaab67c13e031d794f35c3a678b74d2ec19ae9014f6bdca43879c33421c`](https://etherscan.io/tx/0x8640dfaab67c13e031d794f35c3a678b74d2ec19ae9014f6bdca43879c33421c)

---

Here is your **final unified `README.md`**, precisely merged and minimally formatted.
It retains your canonical abstract, Lean instructions, and all factual Ethereum verification data in one authoritative file.

---

````markdown
# Substrate Theory — Canonical Repository

> This repository contains the canonical specification, the **verbatim** Lean 4 formalization, and the verified Ethereum on-chain record of *Substrate Theory – Canonical Edition*.

---

## Abstract

We present a complete formal system establishing quantum mechanics and general relativity
as computational regimes of a single substrate governed by algorithmic complexity thresholds.
The theory is grounded in Kolmogorov complexity, formalized in Lean 4 across 21 modules total-
ing 5 300 + lines, and demonstrates convergence between ideal (noncomputable) and operational (computable)
layers through eight bridge theorems. A critical complexity threshold at 50 bits determines the quantum-classical transition,
with gravity and quantum collapse emerging as the same mechanism. The formalization establishes universal grounding through a rank system and
proposes information-theoretic interpretations of fundamental physical constants.

---

## Build & Verify (Lean 4)

1. **Install Lean toolchain (elan):**
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
# restart your shell then:
lean --version
lake --version
````

2. **Build the project (from repository root):**

```bash
lake update
lake build
```

If the formalization declares external dependencies, they will be fetched by `lake update`.

---

## Canonical On-Chain Record (Ethereum Mainnet)

The canonical text is immutably encoded as EVM bytecode at a verifiable address. The NFT wrapper contract provides ownership and metadata linkage to the canonical text. Both are recorded on Ethereum Mainnet and can be verified independently.

### Contracts

| Contract                                                                                         | Type                 | Address                                      | Verified | Purpose                                      |
| ------------------------------------------------------------------------------------------------ | -------------------- | -------------------------------------------- | -------- | -------------------------------------------- |
| [`OnchainText`](https://etherscan.io/address/0x31218c4d139e373c185732655658315f1892e1ae#code)    | Immutable data store | `0x31218c4d139e373c185732655658315f1892e1ae` | ✅        | Stores the canonical logic text (bytes only) |
| [`OnchainTextNFT`](https://etherscan.io/address/0x9Af3B1e2986Ca245542EF135A24DcF691d57f2E9#code) | ERC-721 wrapper      | `0x9Af3B1e2986Ca245542EF135A24DcF691d57f2E9` | ✅        | Mints NFT linking to the canonical text      |

---

### Content Verification

| Field                      | Value                                                                |
| -------------------------- | -------------------------------------------------------------------- |
| **Canonical File**         | `SUBSTRATE_THEORY.txt`                                               |
| **Size**                   | 11 290 bytes                                                         |
| **Keccak-256 Hash**        | `0x552901c27d17488e6edea08f34db085f2959bcc8eb3f7f0c8869560c4f89ec09` |
| **contentHash (on-chain)** | identical                                                            |

To verify locally:

```bash
cast code 0x31218c4d139e373c185732655658315f1892e1ae --rpc-url https://ethereum.publicnode.com > code.hex
sed 's/^0x//' code.hex | xxd -r -p > substrate.txt
cast keccak "0x$(xxd -p -c 999999 substrate.txt)"
# → 0x552901c27d17488e6edea08f34db085f2959bcc8eb3f7f0c8869560c4f89ec09
```

---

### Key Transactions

| Description              | Tx Hash                                                                                                                                                            | Block (approx.)      |
| ------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------ | -------------------- |
| NFT Contract Deployment  | [`0xe820a42226839735519c3eb12d46ae8d73d06c203c13b6caf38c065d6e2bc7b0`](https://etherscan.io/tx/0xe820a42226839735519c3eb12d46ae8d73d06c203c13b6caf38c065d6e2bc7b0) | Mainnet (2025-11-07) |
| Text Contract Deployment | [`0xaf60585cb51e4eb289a0babf1fc3c66a17e3244ed26874fbfe505f8b433e916f`](https://etherscan.io/tx/0xaf60585cb51e4eb289a0babf1fc3c66a17e3244ed26874fbfe505f8b433e916f) | Mainnet (2025-11-07) |
| Mint Token #1            | [`0x8640dfaab67c13e031d794f35c3a678b74d2ec19ae9014f6bdca43879c33421c`](https://etherscan.io/tx/0x8640dfaab67c13e031d794f35c3a678b74d2ec19ae9014f6bdca43879c33421c) | Mainnet (2025-11-07) |

---

## Academic Citation

> Scherf, M. (2025). *Substrate Theory – Canonical Logical Specification (Ethereum On-Chain Reference).*
> Contracts `0x31218c4d139e373c185732655658315f1892e1ae` and `0x9Af3B1e2986Ca245542EF135A24DcF691d57f2E9` (verified on Ethereum Mainnet).
> Keccak-256 `0x552901c27d17488e6edea08f34db085f2959bcc8eb3f7f0c8869560c4f89ec09`.

---

**External Links:**

* [`OnchainText`](https://etherscan.io/address/0x31218c4d139e373c185732655658315f1892e1ae#code)
* [`OnchainTextNFT`](https://etherscan.io/address/0x9Af3B1e2986Ca245542EF135A24DcF691d57f2E9#code)

---

```

---

Would you like me to include the brief **table of module counts and theorem categories** from the Lean formalization (Types, Axioms, Theorems, Bounds, etc.) beneath the abstract section for completeness, or keep this purely on-chain + build-related?
```
