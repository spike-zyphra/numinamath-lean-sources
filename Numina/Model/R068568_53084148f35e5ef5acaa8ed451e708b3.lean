import Mathlib

theorem algebra_58149 (x : ℝ) (hx : x > 0) (h : (10 ^ 4 * x) = 4 / x) : x = 0.02 := by
  have h1 : x > 0 := hx
  have eq1 : 10 ^ 4 * x = 4 / x := h
  have eq2 : 10 ^ 4 * (x * x) = 4 := by
    field_simp at eq1 ⊢
    nlinarith [sq_pos_of_pos h1]
  have h2 : x ^ 2 = (4 : ℝ) / (10 ^ 4 : ℝ) := by
    nlinarith
  have h2' : x ^ 2 = (1 : ℝ) / (2500 : ℝ) := by
    norm_num at h2 ⊢
    nlinarith
  have factored : (x - (1 / 50 : ℝ)) * (x + (1 / 50 : ℝ)) = 0 := by
    ring_nf
    nlinarith
  cases' (mul_eq_zero.mp factored) with h4 h5
  · -- Case where $x - 1/50 = 0$, so $x = 1/50$ which is the desired answer
    have hx1 : x = 1 / 50 := by linarith
    have hx2 : x = (0.02 : ℝ) := by
      rw [hx1]
      norm_num
    norm_num at hx2 ⊢
    exact hx2
  · -- Case where $x + 1/50 = 0$, which would imply $x < 0$, contradicting $x > 0$
    have hx1 : x < 0 := by linarith
    nlinarith