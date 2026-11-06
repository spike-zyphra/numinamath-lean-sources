import Mathlib

theorem algebra_297202 {x y : ℝ} (h₀ : x + y + x * y + 1 = 0) (h₁ : x ^ 2 * y + x * y ^ 2 + 2 = 0) :
    (x - y) ^ 2 = 0 ∨ (x - y) ^ 2 = 9 := by
  have h2 : (x + 1) * (y + 1) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h2) with h3 h4
  · -- Case where x + 1 = 0, so x = -1
    have hx : x = -1 := by linarith
    rw [hx] at h₁
    have hy : y ^ 2 - y - 2 = 0 := by
      nlinarith
    have h5 : (y - 2) * (y + 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h5) with hy2 hy1
    · -- Case where y = 2
      have hy2' : y = 2 := by linarith
      have h6 : (x - y) ^ 2 = 9 := by
        rw [hx, hy2']
        norm_num
      right
      linarith
    · -- Case where y = -1
      have hy1' : y = -1 := by linarith
      have h7 : (x - y) ^ 2 = 0 := by
        rw [hx, hy1']
        norm_num
      left
      linarith
  · -- Case where y + 1 = 0, so y = -1
    have hy : y = -1 := by linarith
    rw [hy] at h₁
    have hx : x ^ 2 - x - 2 = 0 := by
      nlinarith
    have h6 : (x - 2) * (x + 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h6) with hx2 hx1
    · -- Case where x = 2
      have hx2' : x = 2 := by linarith
      have h7 : (x - y) ^ 2 = 9 := by
        rw [hx2', hy]
        norm_num
      right
      linarith
    · -- Case where x = -1
      have hx1' : x = -1 := by linarith
      have h8 : (x - y) ^ 2 = 0 := by
        rw [hx1', hy]
        norm_num
      left
      linarith