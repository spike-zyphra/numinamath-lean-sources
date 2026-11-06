import Mathlib

theorem algebra_93828 {x : ℝ} (hx : x > 0) (h : (x * 10000) = 4 / x) : x = 0.02 := by
  have h1 : x ^ 2 - 1 / 2500 = 0 := by
    field_simp at h ⊢
    nlinarith
    all_goals nlinarith
  have h2 : (x - 1 / 50) * (x + 1 / 50) = 0 := by
    nlinarith [h1]
  cases' (mul_eq_zero.mp h2) with h3 h4
  · -- Case where x - 1/50 = 0, thus x = 1/50 = 0.02
    have hx2 : x = 1 / 50 := by linarith
    rw [hx2]
    norm_num
  · -- Case where x + 1/50 = 0, contradicting x > 0
    have h5 : x < 0 := by linarith
    linarith