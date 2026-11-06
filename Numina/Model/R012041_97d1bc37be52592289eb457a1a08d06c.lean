import Mathlib

open Real

theorem algebra_170339 :
  IsGreatest {A | ∃ x : ℝ, A = sin x * cos x ∧ sin x > 0 ∧ cos x > 0} (1/2) := by
  constructor
  · -- Show 1/2 is in the set
    use (Real.pi / 4)
    have h1 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [sin_pi_div_four]
    have h2 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [cos_pi_div_four]
    constructor
    · -- Show the area is 1/2
      rw [h1, h2]
      have h3 : (Real.sqrt 2 / 2 : ℝ) * (Real.sqrt 2 / 2) = 1 / 2 := by
        nlinarith [Real.sqrt_pos.mpr (show 0 < 2 by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
      nlinarith
    constructor
    · -- Show sin x > 0
      rw [h1]
      have h4 : Real.sqrt 2 > 0 := by
        positivity
      positivity
    · -- Show cos x > 0
      rw [h2]
      have h4 : Real.sqrt 2 > 0 := by
        positivity
      positivity
  · -- Show no value greater than 1/2 is in the set
    intro A hA
    rcases hA with ⟨x, hA_eq, h1, h2⟩
    have h3 : sin x * cos x ≤ 1 / 2 := by
      have h4 : sin x * cos x = (1 / 2) * sin (2 * x) := by
        rw [sin_two_mul]
        <;> ring
      rw [h4]
      have h5 : sin (2 * x) ≤ 1 := by 
        apply sin_le_one
      nlinarith
    nlinarith [hA_eq, h3]