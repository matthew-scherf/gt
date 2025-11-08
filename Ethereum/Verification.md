# Substrate Theory — Canonical On-Chain Deployment (Ethereum Mainnet)

**Author:** Matthew Scherf  
**Date:** 2025-11-08  
**Network:** Ethereum Mainnet  
**Deployer Address:** `0x367E6B384b6Ec96Ccec478F7B314d3deB2F01195`  
**Verifier:** Etherscan 
---

##  Overview

This deployment permanently anchors the canonical logical specification of **Substrate Theory**—the formal foundation for *Only-One / The Unique Ontic Substrate*—onto the Ethereum mainnet as an immutable on-chain text artifact.  
It consists of two verified contracts:

| Contract | Type | Address | Verified | Purpose |
|-----------|------|----------|-----------|----------|
| [`OnchainText`](https://etherscan.io/address/0x60bd91334E96813bA78ac76b5E71f641057E5A28#code) | Immutable data store | `0x60bd91334E96813bA78ac76b5E71f641057E5A28` | ✅ | Stores raw canonical logic bytes |
| [`OnchainTextNFT`](https://etherscan.io/address/0x9Af3B1e2986Ca245542EF135A24DcF691d57f2E9#code) | ERC-721 wrapper | `0x9Af3B1e2986Ca245542EF135A24DcF691d57f2E9` | ✅ | Mints NFT that references the above bytes |

---

##  Immutable Content Verification

| Field | Value |
|--------|--------|
| **File** | `SUBSTRATE_THEORY.txt` |
| **Size** | 11 290 bytes |
| **Keccak-256 Hash** | `0x552901c27d17488e6edea08f34db085f2959bcc8eb3f7f0c8869560c4f89ec09` |
| **contentHash (on-chain)** | identical |

### Verify Locally
```bash
# Hash the file you published
xxd -p -c 999999 SUBSTRATE_THEORY.txt | cast keccak
# Expected output:
# 0x552901c27d17488e6edea08f34db085f2959bcc8eb3f7f0c8869560c4f89ec09
````

---

## 🖼 NFT Metadata Integrity

| Property         | Value                                            |
| ---------------- | ------------------------------------------------ |
| Token ID         | `1`                                              |
| Owner            | `0x367E6B384b6Ec96Ccec478F7B314d3deB2F01195`     |
| getApproved      | `0x0000000000000000000000000000000000000000`     |
| isApprovedForAll | `false`                                          |
| tokenURI         | on-chain JSON referencing `OnchainText` contract |

### Inspect Metadata

```bash
cast call 0x9Af3B1e2986Ca245542EF135A24DcF691d57f2E9 \
  "tokenURI(uint256)(string)" 1 --rpc-url "$ETH_RPC_URL"
```

---

## Key Transactions

| Description              | Tx Hash                                                                                                           | Block      |
| ------------------------ | ----------------------------------------------------------------------------------------------------------------- | ---------- |
| Text contract deployment | [`0x16e141c7…3386c1`](https://etherscan.io/tx/0x16e141c729d2648d92fc610f42f21209b7f999229d1287bf545f4461623386c1) | 23 750 692 |
| NFT contract deployment  | [`0xf0d47870…f64d8`](https://etherscan.io/tx/0xf0d47870fef5051c2053725a820a79922ac4e614131064d4977e83876b7f64d8)  | 23 750 694 |
| Mint token #1            | [`0x44d7fd06…614a4`](https://etherscan.io/tx/0x44d7fd065c1217b7e0b94ddebcf7b49171fedc5432067ffc48872ee89ca614a4)  | 23 750 694 |

---

## Academic Citation

> Scherf, M. (2025). *Substrate Theory – Canonical Logical Specification (Ethereum On-Chain Reference).*
> DOI [to be added e.g. Zenodo]
> Contract `0x60bd91334E96813bA78ac76b5E71f641057E5A28`
> Keccak-256 `0x552901c27d17488e6edea08f34db085f2959bcc8eb3f7f0c8869560c4f89ec09`
> Immutable record on Ethereum Mainnet verifying canonical logic source.

---

