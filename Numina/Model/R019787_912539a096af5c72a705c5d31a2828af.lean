import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_307336 {k m : ℝ} (a b : ℝ)
  (h : ∀ x ∈ Icc a b, |x^2 - k * x - m| ≤ 1) :
  b - a ≤ 2 * sqrt 2 := by
  by_cases h3 : b ≥ a
  · -- Case b ≥ a
    have h1 := h a (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
    have h2 := h b (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
    have h4 : (a + b) / 2 ≥ a := by linarith
    have h5 : (a + b) / 2 ≤ b := by linarith
    have h6 : (a + b) / 2 ∈ Icc a b := ⟨by linarith, by linarith⟩
    have h7 := h ((a + b) / 2) h6
    have h11 : -1 ≤ a^2 - k * a - m ∧ a^2 - k * a - m ≤ 1 := by
      constructor <;> linarith [abs_le.mp h1]
    have h12 : -1 ≤ b^2 - k * b - m ∧ b^2 - k * b - m ≤ 1 := by
      constructor <;> linarith [abs_le.mp h2]
    have h13 : -1 ≤ ((a + b)/2)^2 - k * ((a + b)/2) - m ∧ ((a + b)/2)^2 - k * ((a + b)/2) - m ≤ 1 := by
      constructor <;> linarith [abs_le.mp h7]
    nlinarith [Real.sqrt_nonneg 2, Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (a - b), sq_nonneg ((a + b) ^ 2 - 4 * k * (a + b) + 4 * (k ^ 2 - 2 * m) ), abs_nonneg (b - a), sq_nonneg ((a - ((k) ) : ℝ)), sq_nonneg ((b - ((k) ) : ℝ)), mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2)]
  · -- Case b < a
    have h4 : b - a ≤ 0 := by linarith
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]