import Mathlib

theorem algebra_268070 (p : ℝ) (x y z : ℝ)
    (h₀ : x^2 - 3 * y + p = z) (h₁ : y^2 - 3 * z + p = x) (h₂ : z^2 - 3 * x + p = y) :
    (p ≥ 4 → x = 2 ∧ y = 2 ∧ z = 2) ∧ (p ∈ Set.Ico 1 4 → x = y ∧ y = z) := by 
  constructor 
  · -- Assume p ≥ 4, prove x = 2 ∧ y = 2 ∧ z = 2
    intro hp 
    have h3 : (x - 2) ^ 2 + (y - 2) ^ 2 + (z - 2) ^ 2 = 0 := by 
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z - 2)]
    have hx2 : x = 2 := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z - 2), h3]
    have hy2 : y = 2 := by 
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z - 2), h3]
    have hz2 : z = 2 := by 
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z - 2), h3]
    exact ⟨hx2, hy2, hz2⟩ 
  · -- Assume p ∈ Set.Ico 1 4, prove x = y ∧ y = z 
    intro hp 
    rcases hp with ⟨hp1, hp4⟩ 
    have h5 : (x - y) ^ 2 = 0 := by 
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (p - 1), sq_nonneg (p - 4), mul_nonneg (show 0 ≤ (p - 1 : ℝ) by linarith) (show 0 ≤ (4 - p) by linarith)]
    have hx_eq_y : x = y := by 
      have h4 : x - y = 0 := by 
        rw [sq_eq_zero_iff] at h5 
        linarith 
      linarith 
    have h6 : (y - z) ^ 2 = 0 := by 
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (p - 1), sq_nonneg (p - 4), mul_nonneg (show 0 ≤ (p - 1 : ℝ) by linarith) (show 0 ≤ (4 - p) by linarith)]
    have hy_eq_z : y = z := by 
      have h7 : y - z = 0 := by 
        rw [sq_eq_zero_iff] at h6 
        linarith 
      linarith 
    exact ⟨hx_eq_y, hy_eq_z⟩