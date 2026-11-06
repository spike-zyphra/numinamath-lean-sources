import Mathlib

open Real Set
open scoped Real

theorem calculus_16425 :
  IsGreatest {x | ∃ θ : ℝ, θ ∈ Ioo 0 Real.pi ∧ x = sin (θ / 2) * (1 + cos θ)} (4 * sqrt 3 / 9) := by
  constructor
  · -- Show 4 * sqrt 3 / 9 is in the set.
    use 2 * arcsin (sqrt 3 / 3)
    constructor
    · -- Show θ ∈ (0, π)
      constructor
      · -- Show θ > 0
        have h1 : 0 < arcsin (sqrt 3 / 3) := by
          apply arcsin_pos.2
          have h2 : 0 < sqrt 3 := by
            apply Real.sqrt_pos.2
            norm_num
          linarith [Real.sqrt_nonneg 3]
        nlinarith [h1]
      · -- Show θ < π
        have h3 : arcsin (sqrt 3 / 3) < Real.pi / 2 := by
          apply arcsin_lt_pi_div_two.2
          have h4 : sqrt 3 / 3 < 1 := by
            have h5 : sqrt 3 < 3 := by
              rw [Real.sqrt_lt] <;> norm_num
            linarith
          linarith [Real.sqrt_nonneg 3]
        nlinarith [h3, Real.pi_pos]
    · -- Show x = sin (θ / 2) * (1 + cos θ)
      have h1 : sin (arcsin (sqrt 3 / 3)) = sqrt 3 / 3 := by
        refine sin_arcsin (by linarith [Real.sqrt_nonneg 3]) (by
          have h4 : sqrt 3 < 3 := by
            rw [Real.sqrt_lt] <;> norm_num
          linarith)
      have h3 : sin (2 * arcsin (sqrt 3 / 3) / 2) = sin (arcsin (sqrt 3 / 3)) := by
        ring_nf
      have h4 : cos (2 * arcsin (sqrt 3 / 3)) = 1 - 2 * (sqrt 3 / 3) ^ 2 := by
        have h5 : cos (2 * arcsin (sqrt 3 / 3)) = 1 - 2 * sin (arcsin (sqrt 3 / 3)) ^ 2 := by
          rw [cos_two_mul]
          rw [sin_sq]
          all_goals ring
        rw [h1] at h5
        linarith
      have h5 : 1 + cos (2 * arcsin (sqrt 3 / 3)) = 2 * (1 - (sqrt 3 / 3) ^ 2) := by
        linarith [h4]
      rw [h3, h5]
      have h6 : (sqrt 3 / 3 : ℝ) ^ 2 = (3 : ℝ) / 9 := by
        have h4 : (sqrt 3 : ℝ) ^ 2 = (3 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
        field_simp
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
      nlinarith [h1, Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  · -- Show 4 * sqrt 3 / 9 is an upper bound
    intro x hx
    rcases hx with ⟨θ, hθ, hx⟩
    rcases hθ with ⟨hθ1, hθ2⟩
    have h1 : 0 < θ / 2 := by linarith [hθ1]
    have h2 : θ / 2 < Real.pi / 2 := by
      linarith [hθ2, Real.pi_pos]
    have h3 : sin (θ / 2) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      · linarith [hθ1]
      · linarith [h2, Real.pi_pos]
    have h4 : cos θ = 1 - 2 * sin (θ / 2) ^ 2 := by
      have h5 : cos θ = cos (2 * (θ / 2)) := by ring
      rw [h5]
      rw [cos_two_mul]
      rw [sin_sq]
      all_goals ring_nf <;> simp [Real.pi_pos]
    rw [h4] at hx
    nlinarith [sq_nonneg (sin (θ / 2) - sqrt 3 / 3), sq_nonneg (sin (θ / 2)), sq_nonneg (sin (θ / 2) - 1), sq_nonneg (sin (θ / 2) + 1), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), Real.sqrt_nonneg 3, Real.sqrt_nonneg (3 : ℝ)]