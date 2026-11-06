import Mathlib

theorem algebra_19554 (x y : ℝ) (h : ∃ c, x = c * 81 ∧ y = c * x ∧ 3 = c * y) :
    x + y = 36 := by
  rcases h with ⟨c, hx, hy, h3⟩
  have eq1 : 3 = c ^ 3 * 81 := by
    have eq2 : y = c * (c * 81) := by
      rw [hx] at hy
      linarith
    rw [eq2] at h3
    linarith
  have eq2 : c ^ 3 = 1 / 27 := by
    nlinarith
  have hc : c = 1 / 3 := by
    have h1 : c ^ 3 - (1 / 27) = 0 := by
      linarith
    have h2 : 27 * c ^ 3 - 1 = 0 := by
      linarith
    have h3 : (3 * c - 1) * (9 * c ^ 2 + 3 * c + 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h3) with h4 h5
    · -- Case where $3c - 1 = 0$, so $c = 1/3$.
      linarith
    · -- Case where $9c^2 + 3c + 1 = 0$.
      nlinarith [sq_nonneg (c + 1 / 6), sq_nonneg (c), sq_nonneg (c * 3 + 1)]
  have hx' : x = 27 := by
    rw [hx]
    rw [hc]
    norm_num
  have hy' : y = 9 := by
    rw [hy]
    rw [hx']
    rw [hc]
    norm_num
  linarith [hx', hy']