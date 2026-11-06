import Mathlib

open Real

theorem algebra_213997 {f : ℕ → ℝ} (hf : ∀ n, f n = (n - 1) / (n ^ 2 + 1)) :
    IsGreatest (Set.range f) 0.2 ∧ f 2 = 0.2 ∧ f 3 = 0.2 := by
  have h1 : f 2 = 0.2 := by
    rw [hf]
    norm_num
  have h2 : f 3 = 0.2 := by
    rw [hf]
    norm_num
  have h3 : IsGreatest (Set.range f) 0.2 := by
    constructor
    · -- Show 0.2 is in the range
      use 2
      all_goals
        simp [h1]
    · -- Show 0.2 is greatest in the range
      intro y
      rintro ⟨n, hn⟩
      rw [hf] at hn
      have h4 : (n - 1 : ℝ) / (n ^ 2 + 1) ≤ (0.2 : ℝ) := by
        by_cases h : n ≤ 4
        · -- n <= 4
          interval_cases n <;> norm_num at hn ⊢
          <;> try { linarith }
        · -- n > 4
          have h5 : n ≥ 5 := by
            omega
          have h6 : (n : ℝ) ≥ (5 : ℝ) := by
            exact_mod_cast h5
          have h7 : (n ^ 2 + 1 : ℝ) > 0 := by
            nlinarith [sq_nonneg (n : ℝ)]
          have h8 : (n - 1 : ℝ) ≤ (0.2 : ℝ) * (n ^ 2 + 1 : ℝ) := by
            have h11 : (n : ℝ) ≥ (3 : ℝ) := by
              nlinarith [show (n : ℝ) ≥ (5 : ℝ) from by exact_mod_cast h5]
            nlinarith [sq_nonneg ((n : ℝ) - 2.5), sq_nonneg ((n : ℝ) - 3), sq_nonneg ((n : ℝ) - 2), sq_nonneg ((n : ℝ) - 5)]
          apply (div_le_iff₀ (by positivity)).mpr
          linarith
      linarith [hn, h4]
  exact ⟨h3, h1, h2⟩