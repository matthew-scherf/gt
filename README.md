# Substrate Theory — Canonical Repository

> This repository contains the canonical specification, the **verbatim** Lean 4 formalization, and an Ethereum on‑chain verification record. 

## Abstract

We present a complete formal system establishing quantum mechanics and general relativity
as computational regimes of a single substrate governed by algorithmic complexity thresholds.
The theory is grounded in Kolmogorov complexity, formalized in Lean 4 across 21 modules total-
ing 5,300+ lines, and demonstrates convergence between ideal (noncomputable) and operational
(computable) layers through eight bridge theorems. A critical complexity threshold at 50 bits
determines the quantum-classical transition, with gravity and quantum collapse emerging as the
same mechanism. The formalization establishes universal grounding through a rank system and
proposes information-theoretic interpretations of fundamental physical constants.

## Repository Layout

- Lean 4 project files (`lakefile.lean`, `lake-manifest.json`, `lean/` and/or `SubstrateTheory/`) — canonical formalization.
- `onchain/Verification.md` — canonical on‑chain record and independent verification guide.

## Build & Verify (Lean 4)

1. **Install Lean toolchain (elan):**
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
# restart your shell, then:
lean --version
lake --version
```

2. **Build the project (from repository root):**
```bash
lake update
lake build
```

If the formalization declares external dependencies, they will be fetched by `lake update`.

## Canonical On‑Chain Record (Ethereum)

The canonical text is immutably encoded as EVM bytecode at a verifiable address. See `onchain/Verification.md` for the full, reproducible procedure (bytecode retrieval → UTF‑8 decode → `keccak256` hash match).

Key identifiers (as recorded on Ethereum Mainnet):
- **Immutable Bytecode Storage (“dataPointer”)**: `0xc3b5e182EEECfAF0855b68c1ACcddEeeF0091246`
- **Content Hash (keccak256)**: `0x552901c27d17488e6edea08f34db085f2959bcc8eb3f7f0c8869560c4f89ec09`

To verify locally using Foundry:
```bash
cast code 0xc3b5e182EEECfAF0855b68c1ACcddEeeF0091246 --rpc-url https://ethereum.publicnode.com > code.hex
sed 's/^0x//' code.hex | xxd -r -p > substrate.txt
cast keccak "0x$(xxd -p -c 999999 substrate.txt)"
# should output: 0x552901c27d17488e6edea08f34db085f2959bcc8eb3f7f0c8869560c4f89ec09
```

## Citation

Cite the on‑chain canonical edition via the contract address and hash recorded in `onchain/Verification.md`.

---

This repository is intentionally **maximally minimal**: only the canonical formal content and its verification pathways are included.
