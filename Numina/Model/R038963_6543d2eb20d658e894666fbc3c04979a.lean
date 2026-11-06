import Mathlib

open Real Set
open scoped Real

theorem inequalities_44583 (x : ℝ) (hx : x ∈ Ioo 0 (π)) :
    sin x + (1/2)*sin (2*x) + (1/3)*sin (3*x) > 0 := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : sin x > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals
      linarith [hx1, hx2, Real.pi_pos]

  have h2 : sin x + (1 / 2) * sin (2 * x) + (1 / 3) * sin (3 * x) = sin x * (2 + cos x - (4 / 3) * sin x ^ 2) := by
    have h3 : sin (2 * x) = 2 * sin x * cos x := by
      rw [sin_two_mul]
    have h4 : sin (3 * x) = 3 * sin x - 4 * sin x ^ 3 := by
      rw [sin_three_mul]
    rw [h3, h4]
    ring_nf
  have h3 : 2 + cos x - (4 / 3) * sin x ^ 2 > 0 := by
    have h4 : sin x ^ 2 = 1 - cos x ^ 2 := by
      have h5 : sin x ^ 2 + cos x ^ 2 = 1 := by
        exact Real.sin_sq_add_cos_sq x
      linarith [h5]
    rw [h4]
    nlinarith [sq_nonneg (cos x + 3 / 8), sq_nonneg (cos x - 1), sq_nonneg (cos x + 1),
              Real.cos_le_one x, Real.neg_one_le_cos x, sq_nonneg (cos x ^ 2 - 1)]

  rw [h2]
  have h4 : sin x > 0 := h1
  have h5 : sin x * (2 + cos x - (4 / 3) * sin x ^ 2) > 0 := by
    have h4 : sin x > 0 := h1
    have h6 : (2 + cos x - (4 / 3) * sin x ^ 2) > 0 := h3
    nlinarith [h4, h6]
  exact h5