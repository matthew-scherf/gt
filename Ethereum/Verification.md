# Verification Appendix  
### *Substrate Theory — Canonical On-Chain Edition (Ethereum Mainnet)*  
**Author:** Matthew Scherf  
**Date of Deployment:** 2025-11-07  
**License:** MIT  
**Permanent Record:** Ethereum Mainnet

---

## 1. Overview

This document certifies that the full text of *Substrate Theory – Canonical Edition* has been immutably written onto the Ethereum blockchain, encoded as executable bytecode at a verifiable address.  
The text exists not as a URL or pointer, but as *the runtime code itself* of a smart contract — permanently distributed across all Ethereum nodes.

---

## 2. Provenance

| Item | Value |
|------|-------|
| **Primary NFT Contract** | [`0x9Af3B1e2986Ca245542EF135A24DcF691d57f2E9`](https://etherscan.io/address/0x9Af3B1e2986Ca245542EF135A24DcF691d57f2E9) |
| **On-Chain Text Contract** | [`0x60bd91334E96813bA78ac76b5E71f641057E5A28`](https://etherscan.io/address/0x60bd91334E96813bA78ac76b5E71f641057E5A28) |
| **Immutable Bytecode Storage (“dataPointer”)** | [`0xc3b5e182EEECfAF0855b68c1ACcddEeeF0091246`](https://etherscan.io/address/0xc3b5e182EEECfAF0855b68c1ACcddEeeF0091246#code) |
| **Deployment Block** | `#23750692` |
| **Deployer Address** | `0x367E6B384b6Ec96Ccec478F7B314d3deB2F01195` |
| **Network** | Ethereum Mainnet |

---

## 3. Canonical Metadata

| Property | Value |
|-----------|-------|
| **File Name** | `SUBSTRATE_THEORY.txt` |
| **Byte Length** | `11 290` bytes |
| **Hash Function** | `keccak256` |
| **Content Hash** | `0x552901c27d17488e6edea08f34db085f2959bcc8eb3f7f0c8869560c4f89ec09` |

This hash corresponds exactly to the reference file used for deployment and verification.  
Any copy producing the same hash is provably identical to the canonical on-chain text.

---

## 4. Independent Verification Guide

Anyone can verify the integrity of the on-chain text using only public Ethereum tools.

### **A. Retrieve the bytecode**

**Option 1 – via `cast` (Foundry):**
```bash
cast code 0xc3b5e182EEECfAF0855b68c1ACcddEeeF0091246 \
  --rpc-url https://ethereum.publicnode.com > code.hex
````

**Option 2 – via JSON-RPC directly:**

```bash
curl -s -X POST https://ethereum.publicnode.com \
  -H "Content-Type: application/json" \
  --data '{"jsonrpc":"2.0","method":"eth_getCode","params":["0xc3b5e182EEECfAF0855b68c1ACcddEeeF0091246","latest"],"id":1}' \
| jq -r .result > code.hex
```

---

### **B. Decode the bytes to human-readable text**

```bash
sed 's/^0x//' code.hex | xxd -r -p > substrate.txt
```

or use any online **hex → UTF-8** decoder
(e.g. [cryptii.com/pipes/hex-decoder](https://cryptii.com/pipes/hex-decoder)).

---

### **C. Confirm authenticity**

```bash
wc -c substrate.txt
# → 11290
cast keccak "0x$(xxd -p -c 999999 substrate.txt)"
# → 0x552901c27d17488e6edea08f34db085f2959bcc8eb3f7f0c8869560c4f89ec09
```

If both values match, you are reading the exact same file recorded on-chain.

---

## 5. Scholarly Reference

> **Citation (APA)**
> Scherf, M. (2025). *Substrate Theory — Canonical On-Chain Edition (Ethereum Mainnet)* [Smart Contract 0xc3b5e182EEECfAF0855b68c1ACcddEeeF0091246]. Ethereum Blockchain. [https://etherscan.io/address/0xc3b5e182EEECfAF0855b68c1ACcddEeeF0091246#code](https://etherscan.io/address/0xc3b5e182EEECfAF0855b68c1ACcddEeeF0091246#code)

---

## 6. Historical Significance

This deployment represents the first verified instance of a complete philosophical and scientific text recorded as pure EVM bytecode.
It establishes a permanent, censorship-resistant archive where the content itself *is* the contract — an ontological text inseparable from its computational substrate.

---

```
