import Mathlib

/- If $\lceil{\sqrt{x}}\rceil=15$, how many possible integer values of $x$ are there? -/
theorem algebra_12460 :
    Set.ncard {x : ℕ | ⌈Real.sqrt x⌉ = 15} = 29 := by
  -- We show that the set of possible values for x is {x | 196 < x ∧ x ≤ 225}
  have H (x : ℕ) : ⌈Real.sqrt x⌉ = 15 ↔ 196 < x ∧ x ≤ 225 := by
    -- ⌈x⌉ = n ↔ n ≤ x < n + 1
    rw [Int.ceil_eq_iff,
        Real.lt_sqrt (by norm_num),
        Real.sqrt_le_left (by norm_num)]
    norm_num

  -- The set {x | 196 < x ∧ x ≤ 225} is equivalent to the Finset Ioc 196 225
  have K : {x | 196 < x ∧ x ≤ 225} = Finset.Ioc 196 225 := by
    ext x
    simp

  -- The set {x | 196 < x ∧ x ≤ 225} has 29 elements
  rw [Set.ext H, K, Set.ncard_coe_Finset]
  simp
