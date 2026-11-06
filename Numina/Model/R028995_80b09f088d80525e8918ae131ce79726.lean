import Mathlib

open Real Set
open scoped Real

theorem algebra_102895 :
  IsGreatest {y : ℝ | ∃ x, y = (1 + cos x) / (sin x + cos x + 2)} 1 := by
  constructor
  · -- Show that 1 is in the set.
    use -(Real.pi / 2)
    have hcos : cos (-(Real.pi / 2)) = 0 := by
      rw [cos_neg]
      norm_num [cos_pi_div_two]
    have hsin : sin (-(Real.pi / 2)) = -1 := by
      rw [sin_neg]
      norm_num [sin_pi_div_two]
    rw [hcos, hsin]
    norm_num
  · -- Show that for any y in the set, y ≤ 1
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h1 : sin x + cos x + 2 > 0 := by
      nlinarith [sq_nonneg (sin x - cos x), Real.sin_sq_add_cos_sq x, sq_nonneg (sin x + cos x - 1), sq_nonneg (sin x + 1), sq_nonneg (cos x - 1), sq_nonneg (cos x + 1)]
    have h2 : (1 + cos x) / (sin x + cos x + 2) ≤ 1 := by
      have h3 : sin x + cos x + 2 > 0 := h1
      have h4 : (1 + cos x) ≤ sin x + cos x + 2 := by
        nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (sin x + 1), sq_nonneg (cos x - 1)]
      have h5 : (1 + cos x) / (sin x + cos x + 2) ≤ (sin x + cos x + 2) / (sin x + cos x + 2) := by
        apply (div_le_div_right h3).mpr
        linarith
      have h6 : (sin x + cos x + 2) / (sin x + cos x + 2) = 1 := by
        field_simp [h3]
      linarith [h5, h6]
    linarith [hx, h2]