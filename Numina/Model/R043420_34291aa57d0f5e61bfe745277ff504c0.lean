import Mathlib

theorem algebra_199998 (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z)
    (h₂ : x + y + z = 5) (h₃ : x ^ 2 + y ^ 2 + z ^ 2 = 15) (h₄ : x * y * z = -3) :
    (x, y, z) = (1 - Real.sqrt 2, 1 + Real.sqrt 2, 3) := by
  have h₅ : x * y + y * z + z * x = 5 := by
    nlinarith
  have h₆ : (x - 3) * (y - 3) * (z - 3) = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  cases' (mul_eq_zero.mp h₆) with h₈ h₉
  · cases' (mul_eq_zero.mp h₈) with h₁₀ h₁₁
    · -- Case $x = 3$.
      have hx1 : x = 3 := by linarith
      have h₂ : y + z = 2 := by
        linarith [h₂, hx1]
      nlinarith [sq_nonneg (y - 3), sq_nonneg (z - 3)]
    · -- Case $y = 3$.
      have hy1 : y = 3 := by linarith
      have h₂ : x + z = 2 := by
        linarith [h₂, hy1]
      nlinarith [sq_nonneg (x - 3), sq_nonneg (z - 3)]
  · -- Case $z = 3$.
    have h₇' : z = 3 := by linarith
    have h₃₁ : x + y = 2 := by
      linarith [h₂, h₇']
    have eq₁ : (x - (1 - Real.sqrt 2)) * (x - (1 + Real.sqrt 2)) = 0 := by
      have eq : y = 2 - x := by linarith [h₃₁]
      rw [show y = 2 - x by linarith] at h₄ h₅
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have eq₂ : x = 1 - Real.sqrt 2 ∨ x = 1 + Real.sqrt 2 := by
      cases' (mul_eq_zero.1 eq₁) with h₂₂ h₃₃
      · -- First root.
        left
        linarith
      · -- Second root.
        right
        linarith
    cases eq₂ with
    | inl hx1 =>
      have hx1' : x = 1 - Real.sqrt 2 := hx1
      have hy : y = 1 + Real.sqrt 2 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      simp [hx1', hy, h₇']
    | inr hx1 =>
      have hx1' : x = 1 + Real.sqrt 2 := hx1
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]