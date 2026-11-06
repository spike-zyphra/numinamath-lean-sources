import Mathlib
theorem exist_irrat_power_rat : ∃ a b : ℝ, Irrational a ∧ Irrational b
    ∧ ∃ (q : ℚ), a ^ b = q := by
  have h1 : Irrational (Real.sqrt 2) := by
    exact irrational_sqrt_two
  by_cases h2 : Irrational ((Real.sqrt 2) ^ (Real.sqrt 2))
  · use (Real.sqrt 2) ^ (Real.sqrt 2)
    use (Real.sqrt 2)
    constructor
    · exact h2
    · constructor
      · exact h1
      · use 2
        simp only [Rat.cast_ofNat]
        have h1 : (√2 ^ √2) ^ √2 = √2 ^ (√2 * √2 : ℝ) := by
          rw [← Real.rpow_mul]
          ring_nf
          all_goals norm_num
        have h2 : √2 * √2 = (2 : ℝ) := by
          calc
            √2 * √2 = (√2) ^ 2 := by ring
            _ = (2 : ℝ) := by rw [Real.sq_sqrt]; positivity
        rw [h1, h2]
        have h3 : √2 ^ (2 : ℝ) = (2 : ℝ) := by
          have h5 : √2 ^ (2 : ℝ) = (√2) ^ 2 := by
            norm_cast
          rw [h5]
          rw [Real.sq_sqrt]
          all_goals norm_num
        rw [h3]
  · use (Real.sqrt 2)
    use (Real.sqrt 2)
    constructor
    · exact h1
    · constructor
      · exact h1
      · unfold Irrational at h2
        push_neg at h2
        simp only [Set.mem_range] at h2
        obtain ⟨y, hy⟩ := h2
        use y
        exact id (Eq.symm hy)