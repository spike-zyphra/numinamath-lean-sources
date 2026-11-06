import Mathlib

open Real Set
open scoped Real

theorem algebra_254733 {x y : ℝ} (hx : x ∈ Ioo 0 Real.pi) (hy : y ∈ Ioo 0 Real.pi)
    (h : cos (2 * x) * cos y - cos (2 * y) * cos x = cos y - cos x) : x = y := by
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  have h1 : cos (2 * x) = 2 * cos x ^ 2 - 1 := by 
    rw [cos_two_mul]
  have h2 : cos (2 * y) = 2 * cos y ^ 2 - 1 := by
    rw [cos_two_mul]
  rw [h1, h2] at h
  have h3 : (cos x - cos y) * (cos x * cos y + 1) = 0 := by
    nlinarith [h]
  cases' (mul_eq_zero.mp h3) with h4 h5
  · -- Case $\cos x - \cos y = 0$, that is $\cos x = \cos y$
    have h6 : cos x = cos y := by linarith
    have h7 : x = y := by
      by_cases h8 : x < y
      · -- Assume x < y
        have h9 : cos x > cos y := by
          apply Real.cos_lt_cos_of_nonneg_of_le_pi
          all_goals linarith
        linarith [h6, h9]
      by_cases h10 : x > y
      · -- Assume x > y
        have h11 : cos x < cos y := by 
          apply Real.cos_lt_cos_of_nonneg_of_le_pi
          all_goals linarith
        linarith [h6, h11]
      linarith
    linarith
  · -- Case $\cos x \cdot \cos y + 1 = 0$, that is $\cos x \cdot \cos y = -1$
    have h6 : cos x * cos y = -1 := by linarith
    nlinarith [Real.cos_sq_add_sin_sq x, Real.cos_sq_add_sin_sq y, 
          Real.sin_pos_of_pos_of_lt_pi hx1 hx2, Real.sin_pos_of_pos_of_lt_pi hy1 hy2, 
          mul_pos (Real.sin_pos_of_pos_of_lt_pi hx1 hx2) (Real.sin_pos_of_pos_of_lt_pi hy1 hy2)]