import Mathlib

open Real Set

theorem algebra_239820 :
    IsGreatest {y : ℝ | ∃ x : ℝ, y = sin x * (2 - cos x) / (5 - 4 * cos x)} (√3 / 4) := by
  constructor
  · -- Let's prove that √3 / 4 is in the set
    use (Real.pi / 3)
    have h1 : sin (Real.pi / 3) = Real.sqrt 3 / 2 := by
      exact sin_pi_div_three
    have h2 : cos (Real.pi / 3) = 1 / 2 := by
      exact cos_pi_div_three
    rw [h1, h2]
    have h3 : (Real.sqrt 3 / 2 : ℝ) * (2 - (1 / 2 : ℝ)) / (5 - 4 * (1 / 2 : ℝ)) = Real.sqrt 3 / 4 := by
      field_simp
      ring
    linarith [h3]
  · -- Let's prove that √3 / 4 is greatest in the set
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h2 : 5 - 4 * cos x > 0 := by
      nlinarith [Real.cos_le_one x, Real.neg_one_le_cos x]
    have h3 : sin x * (2 - cos x) ≤ (Real.sqrt 3 / 4) * (5 - 4 * cos x) := by
      nlinarith [sq_nonneg (sin x - Real.sqrt 3 / 2), sq_nonneg (cos x - 1 / 2),
                sq_nonneg (cos x + 1 / 2), sq_nonneg (sin x + Real.sqrt 3 / 2),
                Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by linarith),
                sq_nonneg (sin x * cos x), sq_nonneg (sin x - Real.sqrt 3),
                sq_nonneg (cos x - 1 / 2), Real.sin_sq_add_cos_sq x
                ]
    have h4 : sin x * (2 - cos x) / (5 - 4 * cos x) ≤ Real.sqrt 3 / 4 := by
      apply (div_le_iff₀ (show (5 - 4 * cos x : ℝ) > 0 by linarith)).mpr
      linarith [h3]
    linarith [h4, hx]