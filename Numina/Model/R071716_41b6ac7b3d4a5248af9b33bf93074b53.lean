import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_603437 {f : ℝ → ℝ} (hf : f = λ x => (3 + x + x^2)/(1 + x)) :
    IsLeast {y | ∃ x, x > 0 ∧ f x = y} (-1 + 2 * sqrt 3) := by 
  constructor 
  · -- Show that -1 + 2 * sqrt 3 is achievable 
    use Real.sqrt 3 - 1 
    constructor 
    · -- Show that Real.sqrt 3 - 1 > 0 
      have h1 : 1 < Real.sqrt 3 := Real.lt_sqrt_of_sq_lt (by norm_num)
      have h2 : Real.sqrt 3 - 1 > 0 := by linarith 
      linarith 
    · -- Show that f (Real.sqrt 3 - 1) = -1 + 2 * Real.sqrt 3 
      have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by linarith)
      rw [hf]
      field_simp [show Real.sqrt 3 - 1 + 1 ≠ 0 by nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]]
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  · -- Show that -1 + 2 * sqrt 3 is the least element in the set 
    intro y 
    rintro ⟨x, hx, hfx⟩ 
    rw [hf] at hfx 
    have h : (3 + x + x^2) / (1 + x) = y := by 
      simpa using hfx 
    have h4 : 1 + x > 0 := by linarith 
    have h5 : (3 + x + x^2) / (1 + x) ≥ -1 + 2 * Real.sqrt 3 := by 
      have h6 : 3 + x + x^2 ≥ (-1 + 2 * Real.sqrt 3) * (1 + x) := by 
        nlinarith [sq_nonneg (x - (-1 + Real.sqrt 3)), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3]
      apply (le_div_iff₀ h4).mpr 
      linarith 
    linarith