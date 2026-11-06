import Mathlib

theorem algebra_244794 (n : ℕ) :
    ∑ i ∈ Finset.range n, Real.sin (2 * i + 1) = (Real.sin n)^2 / Real.sin 1 := by 
  have h1 : ∀ n : ℕ, ∑ i ∈ Finset.range n, Real.sin (2 * i + 1) = (Real.sin n)^2 / Real.sin 1 := by 
    intro n
    induction n with 
    | zero =>
      simp 
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have h2 : Real.sin (2 * (n : ℕ) + 1) = Real.sin (2 * n + 1 : ℝ) := by ring_nf
      simp [h2]
      have h3 : Real.sin (n + 1 : ℝ) ^ 2 = Real.sin (n : ℝ) ^ 2 + Real.sin 1 * Real.sin (2 * n + 1 : ℝ) := by 
        have h4 : Real.sin (n + 1 : ℝ) = Real.sin (n : ℝ) * Real.cos (1 : ℝ) + Real.cos (n : ℝ) * Real.sin (1 : ℝ) := by
          rw [show (n + 1 : ℝ) = (n : ℝ) + (1 : ℝ) by ring]
          rw [Real.sin_add]
          <;> ring_nf
        have h5 : Real.sin (n + 1 : ℝ) ^ 2 = (Real.sin (n : ℝ) * Real.cos (1 : ℝ) + Real.cos (n : ℝ) * Real.sin (1 : ℝ)) ^ 2 := by
          rw [h4]
        have h8 : Real.sin (2 * n + 1 : ℝ) = Real.sin (2 * n : ℝ) * Real.cos (1 : ℝ) + Real.cos (2 * n : ℝ) * Real.sin (1 : ℝ) := by
          have h9 : Real.sin (2 * n + 1 : ℝ) = Real.sin ((2 * n : ℝ) + (1 : ℝ)) := by ring_nf
          rw [h9]
          rw [Real.sin_add]
          <;> ring_nf
        have h6 : Real.sin (2 * n : ℝ) = 2 * Real.sin (n : ℝ) * Real.cos (n : ℝ) := by
          have h7 : Real.sin (2 * n : ℝ) = 2 * Real.sin (n : ℝ) * Real.cos (n : ℝ) := by
            rw [Real.sin_two_mul]
            <;> ring_nf
          exact h7
        have h7 : Real.cos (2 * n : ℝ) = 2 * Real.cos (n : ℝ)^2 - 1 := by
          have h8 : Real.cos (2 * n : ℝ) = 2 * Real.cos (n : ℝ)^2 - 1 := by
            rw [Real.cos_two_mul]
            <;> ring_nf
          exact h8
        rw [h5, h8, h6, h7]
        have h5' : Real.sin 1 > 0 := by
          apply Real.sin_pos_of_pos_of_lt_pi
          all_goals linarith [Real.pi_gt_three]
        nlinarith [Real.sin_sq_add_cos_sq (n : ℝ), Real.sin_sq_add_cos_sq (1 : ℝ), Real.sin_sq_add_cos_sq (2 * n : ℝ), sq_nonneg (Real.sin (n : ℝ) * Real.sin (1 : ℝ)), sq_nonneg (Real.cos (n : ℝ) * Real.sin (1 : ℝ)), sq_nonneg (Real.sin (n : ℝ) * Real.cos (n : ℝ)), sq_nonneg (Real.cos (n : ℝ)^2 - 1), sq_nonneg (Real.sin (1 : ℝ) * Real.sin (2 * n + 1 : ℝ)), Real.sin_sq_add_cos_sq (n + 1 : ℝ)]
      have h4' : Real.sin (n : ℝ) ^ 2 + Real.sin 1 * Real.sin (2 * n + 1 : ℝ) = Real.sin (n + 1 : ℝ) ^ 2 := by 
        linarith [h3]
      have h5' : Real.sin 1 ≠ 0 := by
        have h1 : Real.sin 1 > 0 := by
          apply Real.sin_pos_of_pos_of_lt_pi
          all_goals linarith [Real.pi_gt_three]
        linarith
      field_simp [h5']
      nlinarith [h4', sq_nonneg (Real.sin (n : ℝ) ^ 2), sq_nonneg (Real.sin (n : ℝ) * Real.sin (1 : ℝ)), sq_nonneg (Real.sin (1 : ℝ) * Real.sin (2 * n + 1 : ℝ)), Real.sin_sq_add_cos_sq (n : ℝ), Real.sin_sq_add_cos_sq (1 : ℝ), Real.sin_sq_add_cos_sq (2 * n + 1 : ℝ)]
  specialize h1 n 
  simpa using h1