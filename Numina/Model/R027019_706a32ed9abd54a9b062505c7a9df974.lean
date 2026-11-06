import Mathlib

open Real Set

theorem algebra_609049 :
    IsLeast {x | ∃ α β : ℝ, x = (2 * cos α + 5 * sin β - 8)^2 + (2 * sin α + 5 * cos β - 15)^2} 100 := by
  constructor
  · -- Show that 100 is in the set
    use arccos (8 / 17), Real.pi / 2 - arccos (8 / 17)
    have h1 : cos (arccos (8 / 17)) = 8 / 17 := by
      apply Real.cos_arccos
      norm_num
      all_goals norm_num
    have h2 : sin (arccos (8 / 17)) = 15 / 17 := by
      have h3 : sin (arccos (8 / 17)) ≥ 0 := by
        apply Real.sin_nonneg_of_nonneg_of_le_pi
        · -- Show 0 ≤ arccos (8 / 17)
          linarith [Real.arccos_nonneg (8 / 17)]
        · -- Show arccos (8 / 17) ≤ Real.pi
          linarith [Real.arccos_le_pi (8 / 17)]
      have h4 : sin (arccos (8 / 17)) ^ 2 + cos (arccos (8 / 17)) ^ 2 = 1 := by
        exact Real.sin_sq_add_cos_sq (arccos (8 / 17))
      rw [h1] at h4
      nlinarith
    have h3 : sin (Real.pi / 2 - arccos (8 / 17)) = cos (arccos (8 / 17)) := by
      rw [Real.sin_pi_div_two_sub]
    have h4 : cos (Real.pi / 2 - arccos (8 / 17)) = sin (arccos (8 / 17)) := by
      rw [Real.cos_pi_div_two_sub]
    rw [h3, h4, h1, h2]
    norm_num
  · -- Show 100 is the minimum
    intro x hx
    rcases hx with ⟨α, β, hx⟩
    have h1 : (2 * cos α + 5 * sin β - 8) ^ 2 + (2 * sin α + 5 * cos β - 15) ^ 2 ≥ 100 := by
      have h2 : (2 * cos α + 5 * sin β) ^ 2 + (2 * sin α + 5 * cos β) ^ 2 ≤ 49 := by
        have h3 : (2 * cos α + 5 * sin β) ^ 2 + (2 * sin α + 5 * cos β) ^ 2 = 29 + 20 * sin (α + β) := by
          have h2 : sin (α + β) = sin α * cos β + cos α * sin β := by
            rw [Real.sin_add]
          have h4 : (2 * cos α + 5 * sin β) ^ 2 + (2 * sin α + 5 * cos β) ^ 2 = 4 * (cos α ^ 2) + 20 * (cos α * sin β) + 25 * (sin β ^ 2) + 4 * (sin α ^ 2) + 20 * (sin α * cos β) + 25 * (cos β ^ 2) := by
            ring
          have h3 : 4 * (cos α ^ 2) + 20 * (cos α * sin β) + 25 * (sin β ^ 2) + 4 * (sin α ^ 2) + 20 * (sin α * cos β) + 25 * (cos β ^ 2) = 4 * (cos α ^ 2 + sin α ^ 2) + 25 * (cos β ^ 2 + sin β ^ 2) + 20 * (cos α * sin β + sin α * cos β) := by
            ring
          rw [h3] at h4
          have h5 : cos α ^ 2 + sin α ^ 2 = 1 := Real.cos_sq_add_sin_sq α
          have h6 : cos β ^ 2 + sin β ^ 2 = 1 := Real.cos_sq_add_sin_sq β
          rw [h5, h6] at h4
          have h7 : cos α * sin β + sin α * cos β = sin (α + β) := by
            rw [Real.sin_add]
            all_goals ring
          nlinarith [h7, h4, Real.sin_le_one (α + β)]
        have h4 : sin (α + β) ≤ 1 := by
          have h7 : sin (α + β) ≤ 1 := by
            apply sin_le_one
          linarith
        nlinarith [Real.sin_le_one (α + β)]
      nlinarith [sq_nonneg ( (2 * cos α + 5 * sin β) - (56 / 17) ), sq_nonneg ( (2 * sin α + 5 * cos β) - (105 / 17) ), Real.cos_sq_add_sin_sq α, Real.cos_sq_add_sin_sq β, sq_nonneg (sin (α + β) - 1), Real.sin_le_one (α + β), Real.sin_sq_add_cos_sq (α + β)
      ]
    linarith