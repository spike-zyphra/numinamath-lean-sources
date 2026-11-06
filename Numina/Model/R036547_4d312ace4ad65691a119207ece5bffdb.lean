import Mathlib
open Real

theorem algebra_197754 {x y : ℝ} (hpos : x + y ≥ 0) (h1 : 2 * √(x + y) + x + y = 8) (h2 : x ^ 3 + y ^ 3 = 40) :
  (x = 2 + √2 ∧ y = 2 - √2) ∨ (x = 2 - √2 ∧ y = 2 + √2) := by
  have h3 : (√(x + y)) ^ 2 = x + y := by
    apply Real.sq_sqrt
    linarith
  have eq1 : 2 * √(x + y) + (√(x + y)) ^ 2 = 8 := by
    nlinarith [h1, h3]
  have hs : √(x + y) = 2 := by
    have h4 : (√(x + y)) ^ 2 + 2 * √(x + y) - 8 = 0 := by
      nlinarith [eq1]
    have h5 : (√(x + y) - 2) * (√(x + y) + 4) = 0 := by
      nlinarith [h4]
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- √(x + y) - 2 = 0
      linarith
    · -- √(x + y) + 4 = 0
      have h8 : √(x + y) = -4 := by linarith
      have h9 : √(x + y) ≥ 0 := by
        apply Real.sqrt_nonneg
      nlinarith [h8, h9]
  have hy : x + y = 4 := by
    calc
      x + y = (√(x + y)) ^ 2 := by
        rw [Real.sq_sqrt]
        linarith [hpos]
      _ = (2) ^ 2 := by
        rw [hs]
      _ = (4 : ℝ) := by
        norm_num
  have h4 : x * y = 2 := by
    have eq2 : x ^ 3 + y ^ 3 = 40 := h2
    have eq3 : x ^ 3 + y ^ 3 = (x + y) ^ 3 - 3 * (x * y) * (x + y) := by
      ring
    rw [eq3] at eq2
    rw [hy] at eq2
    linarith
  have h5 : x ^ 2 - 4 * x + 2 = 0 := by
    have h6 : y = 4 - x := by linarith
    rw [h6] at h4
    linarith
  have h6 : (x - (2 + Real.sqrt 2)) * (x - (2 - Real.sqrt 2)) = 0 := by
    have h7 : x ^ 2 - 4 * x + 2 = 0 := h5
    nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  cases' (mul_eq_zero.mp h6) with h8 h9
  · -- Case x - (2 + Real.sqrt 2) = 0, so x = 2 + Real.sqrt 2
    left
    have hx : x = 2 + Real.sqrt 2 := by linarith
    have hy1 : y = 2 - Real.sqrt 2 := by
      nlinarith
    exact ⟨hx, hy1⟩
  · -- Case x - (2 - Real.sqrt 2) = 0, so x = 2 - Real.sqrt 2
    right
    have hx : x = 2 - Real.sqrt 2 := by linarith
    have hy2 : y = 2 + Real.sqrt 2 := by
      nlinarith
    exact ⟨hx, hy2⟩