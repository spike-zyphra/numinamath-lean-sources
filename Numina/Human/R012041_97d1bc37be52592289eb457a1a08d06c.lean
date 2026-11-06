import Mathlib

open Real

theorem algebra_170339 :
  IsGreatest {A | ∃ x : ℝ, A = sin x * cos x ∧ sin x > 0 ∧ cos x > 0} (1/2) := by
  constructor
  · -- First we need to show that 1/2 is indeed achievable by some x
    use π / 4
    constructor
    · -- Show that sin(π/4) * cos(π/4) = 1/2
      have h1 : sin (π / 4) = sqrt 2 / 2 := sin_pi_div_four
      have h2 : cos (π / 4) = sqrt 2 / 2 := cos_pi_div_four
      rw [h1, h2]
      have h3 : (sqrt 2 / 2 : ℝ) * (sqrt 2 / 2 : ℝ) = 1 / 2 := by
        calc
          (sqrt 2 / 2 : ℝ) * (sqrt 2 / 2 : ℝ)
            = (sqrt 2 * sqrt 2) / 4 := by ring
          _ = (sqrt 2 ^ 2) / 4 := by ring
          _ = (2 : ℝ) / 4 := by rw [sq_sqrt]; positivity
          _ = (1 : ℝ) / 2 := by norm_num
      linarith
    constructor
    · -- Show that sin(π/4) > 0
      have h4 : 0 < sqrt 2 := sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)
      have h1 : sin (π / 4) = sqrt 2 / 2 := sin_pi_div_four
      rw [h1]
      positivity
    · -- Show that cos(π/4) > 0
      have h4 : 0 < sqrt 2 := sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)
      have h2 : cos (π / 4) = sqrt 2 / 2 := cos_pi_div_four
      rw [h2]
      positivity
  · -- Now we have to prove that 1/2 is the greatest value in the set
    intro A hA
    rcases hA with ⟨x, hA_eq, hsin_pos, hcos_pos⟩
    have h1 : sin x ^ 2 + cos x ^ 2 = 1 := sin_sq_add_cos_sq x
    nlinarith [sq_nonneg (sin x - cos x), sin_sq_le_one x, cos_sq_le_one x]
