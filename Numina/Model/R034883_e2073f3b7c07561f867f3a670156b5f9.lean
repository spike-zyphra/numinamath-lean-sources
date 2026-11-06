import Mathlib

theorem algebra_231992 {a : ℕ → ℝ} (ha : ∀ n, (3 - a (n + 1)) * (6 + a n) = 18) (ha0 : a 0 = 3) :
    ∑ i in Finset.range (n + 1), 1 / a i = (2 ^ (n + 2) - n - 3) / 3 := by

  have h1 : ∀ n, a n = 3 / ((2 : ℝ) ^ (n + 1) - 1) := by
    intro n 
    induction n with 
    | zero => 
      rw [ha0]
      norm_num
    | succ n ih =>
      have eq1 := ha n 
      rw [ih] at eq1
      have h2 : a (n + 1) = 3 / ((2 : ℝ) ^ (n + 1 + 1) - 1) := by
        have eq3 : (3 - a (n + 1)) * (6 + (3 / ((2 : ℝ) ^ (n + 1) - 1)) ) = 18 := by 
          simpa using eq1
        have h3 : ((2 : ℝ) ^ (n + 1) - 1) ≠ 0 := by 
          have h11 : ∀ (n : ℕ), (2 : ℝ) ^ (n + 1) - (1 : ℝ) > 0 := by 
            intro n 
            induction n with 
            | zero => 
              norm_num 
            | succ n ih =>
              simp [pow_succ] at ih ⊢ 
              all_goals nlinarith 
          specialize h11 n 
          linarith 
        have eq4 : a (n + 1) * (6 * ((2 : ℝ) ^ (n + 1) - 1) + 3) = 9 := by
          field_simp [h3] at eq3 
          nlinarith 
        have eq5 : a (n + 1) = 3 / ((2 : ℝ) ^ (n + 1 + 1) - 1) := by
          have eq6 : ((2 : ℝ) ^ (n + 1 + 1) - 1) = (2 * ((2 : ℝ) ^ (n + 1) - 1) + 1) := by 
            ring_nf 
          rw [eq6] 
          field_simp [(show (2 * ((2 : ℝ) ^ (n + 1) - 1) + 1) ≠ 0 by
              have h11 : (2 : ℝ) ^ (n + 1) - (1 : ℝ) > 0 := by 
                have h11 : ∀ (n : ℕ), (2 : ℝ) ^ (n + 1) - (1 : ℝ) > 0 := by 
                  intro n 
                  induction n with 
                  | zero => 
                    norm_num 
                  | succ n ih =>
                    simp [pow_succ] at ih ⊢ 
                    all_goals nlinarith 
                specialize h11 n 
                linarith 
              nlinarith [sq_nonneg ((2 : ℝ) ^ (n + 1) - 1)]
          )] at *
          <;> nlinarith 
        exact_mod_cast eq5
      simpa using h2

  have h2 : ∀ n : ℕ, ∑ i in Finset.range (n + 1), 1 / a i = (2 ^ (n + 2) - n - 3) / 3 := by
    intro n
    induction n with
    | zero =>
      norm_num [ha0, h1, Finset.sum_range_succ]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      rw [h1 (n + 1)]
      field_simp
      ring_nf

  exact h2 n