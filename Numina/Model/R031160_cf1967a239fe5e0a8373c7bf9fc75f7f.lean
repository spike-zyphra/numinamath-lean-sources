import Mathlib

open Real Set Matrix
open scoped BigOperators

theorem calculus_11365 :
    IsGreatest {v : ℝ | ∃ θ : ℝ, v = (!![1, 1, 1; 1, 1 + sin θ, 1; 1 + cos θ, 1, 1]).det} (1 / 2) := by
  constructor
  · -- Show 1/2 is in the set
    use (3 * Real.pi / 4)
    have h1 : sin (3 * Real.pi / 4) = Real.sqrt 2 / 2 := by
      have h2 : 3 * Real.pi / 4 = Real.pi - (Real.pi / 4) := by ring
      rw [h2]
      rw [sin_pi_sub]
      have h3 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := sin_pi_div_four
      linarith [h3]
    have h1a : cos (3 * Real.pi / 4) = -Real.sqrt 2 / 2 := by
      have h2a : 3 * Real.pi / 4 = Real.pi - (Real.pi / 4) := by ring
      rw [h2a]
      rw [cos_pi_sub]
      have h3a : cos (Real.pi / 4) = Real.sqrt 2 / 2 := cos_pi_div_four
      linarith [h3a]
    simp [Matrix.det_fin_three, h1, h1a]
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
    nlinarith [h2]
  · -- Show no greater element is in the set
    intro v hv
    rcases hv with ⟨θ, h_eq⟩
    rw [h_eq]
    have h2 : (!![1, 1, 1; 1, 1 + sin θ, 1; 1 + cos θ, 1, 1]).det = - sin θ * cos θ := by 
      simp [Matrix.det_fin_three]
      <;> ring
    rw [h2] at *
    have h1 : - sin θ * cos θ ≤ 1 / 2 := by 
      have h5 : sin θ * cos θ = (1 / 2) * sin (2 * θ) := by
        have h2 : sin (2 * θ) = 2 * sin θ * cos θ := by
          rw [sin_two_mul]
        linarith
      have h6 : - sin θ * cos θ = - (1 / 2) * sin (2 * θ) := by
        have h2 : sin θ * cos θ = (1 / 2) * sin (2 * θ) := by
          have h7 : sin (2 * θ) = 2 * sin θ * cos θ := by
            rw [sin_two_mul]
          nlinarith
        nlinarith [h2]
      rw [h6]
      have h7 : - (1 / 2) * sin (2 * θ) ≤ 1 / 2 := by 
        have h9 : sin (2 * θ) ≥ -1 := by 
          have h9 : sin (2 * θ) ≥ -1 := by 
            linarith [neg_one_le_sin (2 * θ), sin_le_one (2 * θ)]
          linarith [h9]
        nlinarith [sin_le_one (2 * θ)]
      linarith [h7]
    linarith