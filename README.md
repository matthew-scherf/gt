# Substrate Theory

> This repository contains the canonical specification, the verbatim Lean 4 formalization, and the verified Ethereum on-chain record of *Substrate Theory – Canonical Edition*.

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

2. **Build the project**

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
| [`OnchainText`](https://etherscan.io/address/0x31218c4d139e373c185732655658315f1892e1ae#code)    | Immutable data store | `0x31218c4d139e373c185732655658315f1892e1ae` | Yes       | Stores the canonical logic text (bytes only) |
| [`OnchainTextNFT`](https://etherscan.io/address/0x9Af3B1e2986Ca245542EF135A24DcF691d57f2E9#code) | ERC-721 wrapper      | `0x9Af3B1e2986Ca245542EF135A24DcF691d57f2E9` | Yes       | Mints NFT linking to the canonical text      |

---

### Content Verification

| Field                                      | Value                                                                |
| ------------------------------------------ | -------------------------------------------------------------------- |
| **Canonical File**                         | `SUBSTRATE_THEORY.txt`                                               |
| **Size**                                   | 11 290 bytes                                                         |
| **Keccak-256 (canonical content, UTF-8)**  | `0x552901c27d17488e6edea08f34db085f2959bcc8eb3f7f0c8869560c4f89ec09` |
| **Keccak-256 (deployed runtime bytecode)** | `0x7dd220053f5ec52419e2a2de159f7b32946f3d41a342dbf77e15c5ca65d8a0a2` |

> The **canonical content hash** verifies the pure text.
> The **bytecode hash** verifies the exact runtime code at the deployed address.

#### Verify canonical content locally (from a local copy of the text)

```bash
xxd -p -c 999999 SUBSTRATE_THEORY.txt | cast keccak
# → 0x552901c27d17488e6edea08f34db085f2959bcc8eb3f7f0c8869560c4f89ec09
```

#### Verify deployed runtime bytecode (from the chain)

```bash
cast code 0x31218c4d139e373c185732655658315f1892e1ae --rpc-url https://ethereum.publicnode.com > code.hex
sed 's/^0x//' code.hex | xxd -r -p > substrate.txt
cast keccak "0x$(xxd -p -c 999999 substrate.txt)"
# → 0x7dd220053f5ec52419e2a2de159f7b32946f3d41a342dbf77e15c5ca65d8a0a2
```

---

### View On-Chain Text Contents (human-readable)

```bash
# 1) Retrieve the on-chain bytecode
cast code 0x31218c4d139e373c185732655658315f1892e1ae --rpc-url https://ethereum.publicnode.com > code.hex

# 2) Decode to UTF-8 text
sed 's/^0x//' code.hex | xxd -r -p > substrate.txt

# 3) Inspect the contents
less substrate.txt
# or:
cat substrate.txt
# (PowerShell) Get-Content substrate.txt
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
> Keccak-256 (canonical text) `0x552901c27d17488e6edea08f34db085f2959bcc8eb3f7f0c8869560c4f89ec09`.
> Keccak-256 (runtime bytecode) `0x7dd220053f5ec52419e2a2de159f7b32946f3d41a342dbf77e15c5ca65d8a0a2`.

---

**External Links:**

* [`OnchainText`](https://etherscan.io/address/0x31218c4d139e373c185732655658315f1892e1ae#code)
* [`OnchainTextNFT`](https://etherscan.io/address/0x9Af3B1e2986Ca245542EF135A24DcF691d57f2E9#code)

