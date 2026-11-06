import Mathlib

open Nat

/--
There exists some positive integer `k` such that
`49 ∣ choose (2k, k)`.
We verify this by explicitly choosing `k = 25`.
-/
lemma exist_sol : ∃ k, 49 ∣ choose (2 * k) k := by
  use 25
  decide  -- `choose (50, 25) % 49 = 0` evaluates to true

/--
For all `k < 25`, `49` does **not** divide `choose (2k, k)`.
We express this using `k : Fin 25` to encode `k < 25` in the type.
We prove this by brute force using `decide`.
-/
lemma lowerbound : ∀ k : Fin 25, ¬ 49 ∣ choose (2 * k) k := by
  intro k
  fin_cases k <;> decide  -- checks all 0 ≤ k < 25

/--
Define the smallest `k` such that `49 ∣ choose (2k, k)`
using `Nat.find` on the existential witness from `exist_sol`.
-/
noncomputable def smallestKDivChoose : ℕ :=
  Nat.find (by
    -- Supply the witness from `exist_sol`
    exact exist_sol
  )

/--
The smallest positive integer `k` such that `49 ∣ choose (2k, k)` is `k = 25`.
This follows from:
1. `choose (50, 25)` is divisible by 49 (via `exist_sol`)
2. No smaller `k < 25` has this property (via `lowerbound`)
-/
theorem smallest_k_choose_div_49 : smallestKDivChoose = 25 := by
  -- Unfold the definition of `smallestKDivChoose`
  rw [smallestKDivChoose]
  -- Apply Nat.find_eq_iff to characterize minimality
  apply (Nat.find_eq_iff exist_sol).mpr
  constructor
  · -- Show that 49 divides choose (2 * 25, 25)
    decide
  · -- Show no smaller k satisfies the property
    intro n hn
    exact lowerbound ⟨n, hn⟩
