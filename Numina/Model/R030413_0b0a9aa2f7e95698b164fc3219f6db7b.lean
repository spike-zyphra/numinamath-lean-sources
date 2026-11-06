import Mathlib

open Real Set
open scoped Real

theorem algebra_181642 :
    IsLeast {y | ∃ x : ℝ, x ∈ Ioo 0 (π/2) ∧ y = 1/sin x ^ 2 + 12 * sqrt 3 / cos x} 28 := by 
  constructor
  · -- Show that 28 is in the set.
    use Real.pi / 6
    constructor
    · -- Show π/6 ∈ (0, π/2)
      constructor
      · -- Show 0 < π/6
        linarith [Real.pi_pos]
      · -- Show π/6 < π/2
        linarith [Real.pi_pos]
    · -- Compute the value of the function at π/6.
      have hsin : sin (Real.pi / 6) = 1 / 2 := by
        exact sin_pi_div_six
      have hcos : cos (Real.pi / 6) = Real.sqrt 3 / 2 := by
        exact cos_pi_div_six
      rw [hsin, hcos]
      field_simp
      <;> ring_nf 
      <;> norm_num
  · -- Show that 28 is minimum
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    rcases hx with ⟨hx1, hx2⟩
    have h1 : 0 < x := hx1
    have h2 : x < Real.pi / 2 := hx2
    have h3 : sin x > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      all_goals linarith [Real.pi_pos]
    have h4 : cos x > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      · linarith [h1, Real.pi_pos]
      · linarith [h2, Real.pi_pos]
    have h5 : 1 / sin x ^ 2 + 12 * Real.sqrt 3 / cos x ≥ 28 := by
      have h6 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
      have pos1 : sin x ^ 2 > 0 := by nlinarith
      have pos2 : cos x > 0 := h4
      have h7 : cos x + 12 * Real.sqrt 3 * sin x ^ 2 - 28 * sin x ^ 2 * cos x ≥ 0 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
              sq_nonneg (sin x - 1 / 2), 
              sq_nonneg (cos x - Real.sqrt 3 / 2), 
              sq_nonneg (sin x ^ 2 - 1 / 4), 
              sq_nonneg (sin x - (1 / 2) ), 
              sq_nonneg (sin x - (Real.sqrt 3 / 2) ), 
              sq_nonneg (cos x - Real.sqrt 3 / 2), 
              Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), 
              Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
              mul_pos h3 h4, 
              h6
            ]
      have h8 : 1 / sin x ^ 2 + 12 * Real.sqrt 3 / cos x - 28 ≥ 0 := by
        have pos1 : sin x ^ 2 > 0 := by nlinarith
        have pos2 : cos x > 0 := h4
        have eq2 : (1 / sin x ^ 2 + 12 * Real.sqrt 3 / cos x - 28) = (cos x + 12 * Real.sqrt 3 * sin x ^ 2 - 28 * sin x ^ 2 * cos x) / (sin x ^ 2 * cos x) := by
          field_simp
          <;> ring
        rw [eq2]
        apply div_nonneg
        linarith
        positivity
      linarith
    linarith