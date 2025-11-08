# Grounding.lean Compilation Fixes

## Errors Fixed

### 1. Line 20: Function Definition Order (CRITICAL)
**Error:** `grounds_C` used before defined in axiom `groundsC_to_ideal`

**Fix:** Moved `grounds_C` definition from line 23 to line 20, BEFORE the axiom that references it:
```lean
def grounds_C (e₁ e₂ : Entity) (p : ℕ) : Prop :=
  C_cond e₁ e₂ p < C e₂ p - C e₁ p + c_grounding

axiom groundsC_to_ideal (e₁ e₂ : Entity) (p : ℕ) :
  grounds_C e₁ e₂ p → grounds e₁ e₂
```

### 2. Line 63: Missing Decidability Instance
**Error:** `failed to synthesize DecidablePred fun parent => grounds_C parent e p`

**Fix:** Added `open Classical in` to enable classical decidability:
```lean
open Classical in
noncomputable def parents_C (e : Entity) (S : Finset Entity) (p : ℕ) : Finset Entity :=
  S.filter (fun (parent : Entity) => grounds_C parent e p)
```

### 3. Line 72: Invalid Empty Check
**Error:** `Invalid field 'Empty': The environment does not contain Finset.Empty`

**Fix:** Changed `current_level.Empty` to `current_level = ∅`:
```lean
if current_level = ∅ then
  Finset.empty
```

### 4. Lines 75-78: Multiple Decidability Issues
**Errors:**
- `failed to synthesize DecidableEq (Entity × ℕ)`
- `failed to synthesize DecidableEq Entity`
- `failed to synthesize Union (Finset Entity)`
- `failed to synthesize Union (Finset (Entity × ℕ))`

**Fix:** Added `open Classical in` to bfs_depth_C_aux:
```lean
@[simp]
open Classical in
noncomputable def bfs_depth_C_aux (p : ℕ) (S : Finset Entity) ...
```

### 5. Line 88: Pattern Matching Syntax Error
**Error:** `unexpected token 'by'; expected 'with'`

**Fix:** Changed `match ... by` to `match ... with` and used `max?` instead of `max`:
```lean
open Classical in
noncomputable def bfs_depth_C (e : Entity) (p : ℕ) (S : Finset Entity) : ℕ :=
  let all_depths := bfs_depth_C_aux p S {Ω} {Ω} 0
  match (all_depths.filter (fun (x, d) => x = e)).max? with
    | some (_, depth) => depth
    | none => 0
```

### 6. Line 98: Unused Variables Warning
**Warning:** `unused variable 'e', 'S', 'p'`

**Fix:** Prefixed unused parameters with underscore:
```lean
noncomputable def bfs_grounding_path (_e : Entity) (_S : Finset Entity) (_p : ℕ) : Option (List Entity) :=
  none
```
