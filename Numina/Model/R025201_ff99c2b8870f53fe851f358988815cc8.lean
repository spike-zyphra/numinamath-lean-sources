import Mathlib

open Real Set
open scoped Real

theorem algebra_320083 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = sin x ^ 4 + sin x * cos x + cos x ^ 4) :
  IsGreatest (range f) (9/8) := by
  constructor
  · -- Show 9/8 is in the range of f
    use Real.pi / 12
    rw [h₀]
    have h1 : sin (Real.pi / 12) ^ 4 + sin (Real.pi / 12) * cos (Real.pi / 12) + cos (Real.pi / 12) ^ 4 = 9 / 8 := by
      have h2 : sin (Real.pi / 12) * cos (Real.pi / 12) = 1 / 4 := by
        have h3 : sin (2 * (Real.pi / 12)) = 2 * sin (Real.pi / 12) * cos (Real.pi / 12) := by
          rw [sin_two_mul]
        have h4 : sin (2 * (Real.pi / 12)) = 1 / 2 := by
          have h5 : 2 * (Real.pi / 12) = Real.pi / 6 := by ring
          rw [h5]
          exact sin_pi_div_six
        have h6 : 2 * sin (Real.pi / 12) * cos (Real.pi / 12) = 1 / 2 := by
          linarith [h3, h4]
        have h7 : sin (Real.pi / 12) * cos (Real.pi / 12) = 1 / 4 := by
          nlinarith
        linarith
      have h3 : sin (Real.pi / 12) ^ 4 + cos (Real.pi / 12) ^ 4 = 7 / 8 := by
        have h4 : sin (Real.pi / 12) ^ 2 + cos (Real.pi / 12) ^ 2 = 1 := by
          exact Real.sin_sq_add_cos_sq (Real.pi / 12)
        have h5 : sin (Real.pi / 12) * cos (Real.pi / 12) = 1 / 4 := h2
        have h6 : sin (Real.pi / 12) ^ 4 + cos (Real.pi / 12) ^ 4 =
            (sin (Real.pi / 12) ^ 2 + cos (Real.pi / 12) ^ 2) ^ 2 - 2 * (sin (Real.pi / 12) * cos (Real.pi / 12)) ^ 2 := by
          ring
        rw [h6, h4, h5]
        norm_num
      linarith [h2, h3]
    linarith [h1]
  · -- Show that 9/8 is the maximum value
    intro y
    rintro ⟨x, hx⟩
    rw [h₀] at hx
    have h2 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    nlinarith [sq_nonneg (sin x ^ 2 - cos x ^ 2), sq_nonneg (sin x - cos x), sq_nonneg (2 * sin x * cos x - 1), Real.sin_sq_add_cos_sq x, sq_nonneg (sin x * cos x - 1 / 4), sq_nonneg (sin x ^ 2 - 1 / 4), sq_nonneg (cos x ^ 2 - 1 / 4), sq_nonneg (sin x ^ 2 - cos x ^ 2), sq_nonneg (sin x), sq_nonneg (cos x)]