import Mathlib
open Real

theorem inequalities_611084: 
    IsLeast {x : ℝ | ∀ a : ℝ, a ≥ 0 → a ≥ 14 * √ a - x} 49 := by

  constructor
  · -- Let's prove that 49 is in the set.
    intro a ha
    have h1 : a ≥ 0 := by linarith
    have h2 : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt (by linarith)
    have h4 : Real.sqrt a ^ 2 - 14 * Real.sqrt a + 49 ≥ 0 := by
      have h5 : (Real.sqrt a - 7) ^ 2 ≥ 0 := by
        apply sq_nonneg
      nlinarith
    have h3 : a + 49 ≥ 14 * Real.sqrt a := by
      nlinarith [Real.sqrt_nonneg a, Real.sq_sqrt (show 0 ≤ a by linarith)]
    linarith
  · -- Let's prove the minimality of 49.
    intro x hx
    have h7 : ∀ a : ℝ, a ≥ 0 → a ≥ 14 * √ a - x := hx
    have h8 := h7 49 (by norm_num)
    have h9 : Real.sqrt (49 : ℝ) = 7 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h9] at h8
    linarith