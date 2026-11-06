import Mathlib

theorem algebra_296587 (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = Real.sqrt 3 * Real.sin (2 * x) + 2 * Real.sin x + 4 * Real.sqrt 3 * Real.cos x) :
    IsGreatest (Set.image f (Set.univ : Set ℝ)) (17 / 2) := by
  constructor
  · -- Show that 17/2 is in the image of f
    use Real.pi / 6
    have h1 : Real.sin (Real.pi / 6) = 1 / 2 := Real.sin_pi_div_six
    have h2 : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := Real.cos_pi_div_six
    have h3 : Real.sin (2 * (Real.pi / 6)) = Real.sqrt 3 / 2 := by
      have h10 : 2 * (Real.pi / 6) = Real.pi / 3 := by
        ring
      rw [h10]
      have h12 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
      linarith
    rw [h₀]
    simp only [h1, h2, h3]
    constructor
    · -- Show that Real.pi / 6 is in Set.univ
      simp
    · -- Show that f (Real.pi / 6) = 17/2
      have h4 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
      nlinarith [Real.sqrt_nonneg 3, h4]
  · -- Show that 17/2 is the greatest element in the image
    intro y
    rintro ⟨x, hx⟩
    rw [h₀] at hx
    have h2 : Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := by
      rw [Real.sin_two_mul]
    rw [h2] at hx
    have h3 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg (Real.sin x - 1 / 2), sq_nonneg (Real.cos x - Real.sqrt 3 / 2), sq_nonneg (Real.sin x - Real.sqrt 3 / 2), sq_nonneg (Real.sin x * Real.sqrt 3 - 1 / 2 * 3), sq_nonneg (Real.sin x - Real.sqrt 3 / 2), sq_nonneg (Real.sin x - 1 / 2 * Real.sqrt 3) ]