import Mathlib

open Real Set
open scoped Real

theorem algebra_176834 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = 7 * sin x ^ 2 + 5 * cos x ^ 2 + 2 * sin x) :
  IsLeast (range f) 4.5 := by
  constructor
  · -- Show that 4.5 is achievable by the function
    use -(Real.pi / 6)
    have h1 : sin (-(Real.pi / 6)) = -1 / 2 := by
      rw [sin_neg]
      have h2 : sin (Real.pi / 6) = 1 / 2 := sin_pi_div_six
      linarith
    have h2 : cos (-(Real.pi / 6)) = Real.sqrt 3 / 2 := by
      rw [cos_neg]
      have h3 : cos (Real.pi / 6) = Real.sqrt 3 / 2 := cos_pi_div_six
      linarith
    rw [h₀ (-(Real.pi / 6))]
    rw [h1, h2]
    have h4 : Real.sqrt 3 ^ 2 = 3 := by
      exact Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
    nlinarith [Real.sqrt_nonneg 3, h4]
  · -- Show that 4.5 is the least value of the function
    intro y
    rintro ⟨x, hx⟩
    rw [h₀ x] at hx
    have h3 : sin x ^ 2 + cos x ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq x
    have h4 : 7 * sin x ^ 2 + 5 * cos x ^ 2 + 2 * sin x = 2 * sin x ^ 2 + 2 * sin x + 5 := by
      have h5 : cos x ^ 2 = 1 - sin x ^ 2 := by
        linarith [h3]
      rw [h5]
      linarith
    rw [h4] at hx
    have h5 : (sin x + 1 / 2) ^ 2 ≥ 0 := by
      have h6 : -1 ≤ sin x := by apply neg_one_le_sin
      have h7 : sin x ≤ 1 := by apply sin_le_one
      nlinarith
    nlinarith [Real.sin_sq_add_cos_sq x, hx, h5, Real.sin_le_one x, Real.neg_one_le_sin x]