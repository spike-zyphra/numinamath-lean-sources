import Mathlib

open Real Set
open scoped BigOperators

theorem number_theory_156987 :
  ∑ᶠ n ∈ {n : ℕ | 0 < n ∧ logb 10 n < 1 / 2}, n = 6 := by
  have h1 : {n : ℕ | 0 < n ∧ logb 10 n < 1 / 2} = {1, 2, 3} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- First, show that if n is in the left side, then n is in the right side.
      intro h
      rcases h with ⟨hn_pos, h2⟩
      have h3 : n ≥ 1 := by linarith
      by_cases h4 : n ≤ 3
      · interval_cases n <;> norm_num [logb_lt_iff_lt_rpow, logb_pos] at h2 ⊢
        <;> norm_num [h4] at *
      · -- n > 3
        have h5 : n ≥ 4 := by omega
        have h6 : logb 10 n ≥ 1 / 2 := by
          have h7 : n ≥ 4 := h5
          have h8 : (n : ℝ) ≥ (4 : ℝ) := by exact_mod_cast h7
          have h11 : logb (10 : ℝ) (n : ℝ) ≥ logb (10 : ℝ) (4 : ℝ) := by
            apply Real.logb_le_logb_of_le
            all_goals norm_num
            all_goals
              have h8 : (n : ℝ) ≥ (4 : ℝ) := h8
              linarith
          have h12 : logb (10 : ℝ) (4 : ℝ) > (1 / 2 : ℝ) := by
            have h13 : log (4 : ℝ) > (log (10 : ℝ) / 2 : ℝ) := by
              have h14 : log (4 : ℝ) > log (Real.sqrt (10 : ℝ)) := by
                apply Real.log_lt_log
                all_goals norm_num
                <;> nlinarith [Real.sqrt_nonneg (10 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num)]
              have h15 : log (Real.sqrt (10 : ℝ)) = (log (10 : ℝ) / 2 : ℝ) := by
                calc
                  log (Real.sqrt (10 : ℝ)) = log ((10 : ℝ) ^ (1 / 2 : ℝ)) := by
                    rw [Real.sqrt_eq_rpow]
                  _ = (1 / 2 : ℝ) * log (10 : ℝ) := by
                    rw [log_rpow]
                    all_goals linarith
                  _ = (log (10 : ℝ) / 2 : ℝ) := by
                    ring
              linarith [h14, h15]
            have h14 : logb (10 : ℝ) (4 : ℝ) = log (4 : ℝ) / log (10 : ℝ) := by
              field_simp [logb]
            rw [h14]
            have h15 : log (10 : ℝ) > 0 := by
              apply Real.log_pos
              all_goals norm_num
            apply (lt_div_iff₀ h15).mpr
            nlinarith [h13, Real.log_pos (show (10 : ℝ) > 1 by norm_num)]
          linarith [h11, h12]
        linarith [h6, h2]
    · -- Show that if n is in the right side, then n is in the left side.
      intro h
      rcases h with (rfl | rfl | rfl)
      · constructor
        · norm_num
        · -- Show logb 10 1 < 1/2
          have h1_10 : logb (10 : ℝ) (1 : ℝ) = 0 := by
            simp [logb]
          norm_num [h1_10] at *
      · constructor
        · norm_num
        · -- Show logb 10 2 < 1/2
          have h2_10 : logb (10 : ℝ) (2 : ℝ) < (1 / 2 : ℝ) := by
            have h3 : log (2 : ℝ) < (log (10 : ℝ) / 2 : ℝ) := by
              have h4 : log (2 : ℝ) < log (Real.sqrt (10 : ℝ)) := by
                apply Real.log_lt_log
                all_goals norm_num
                <;> nlinarith [Real.sqrt_nonneg (10 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num)]
              have h5 : log (Real.sqrt (10 : ℝ)) = (log (10 : ℝ) / 2 : ℝ) := by
                calc
                  log (Real.sqrt (10 : ℝ)) = log ((10 : ℝ) ^ (1 / 2 : ℝ)) := by
                    rw [Real.sqrt_eq_rpow]
                  _ = (1 / 2 : ℝ) * log (10 : ℝ) := by
                    rw [log_rpow]
                    all_goals linarith
                  _ = (log (10 : ℝ) / 2 : ℝ) := by
                    ring
              linarith [h4, h5]
            have h4 : logb (10 : ℝ) (2 : ℝ) = log (2 : ℝ) / log (10 : ℝ) := by
              field_simp [logb]
            rw [h4]
            have h5 : log (10 : ℝ) > 0 := by
              apply Real.log_pos
              all_goals norm_num
            apply (div_lt_iff₀ h5).mpr
            nlinarith [h3, Real.log_pos (show (10 : ℝ) > 1 by norm_num)]
          norm_num [h2_10] at *
      · constructor
        · norm_num
        · -- Show logb 10 3 < 1/2
          have h3_10 : logb (10 : ℝ) (3 : ℝ) < (1 / 2 : ℝ) := by
            have h3 : log (3 : ℝ) < (log (10 : ℝ) / 2 : ℝ) := by
              have h4 : log (3 : ℝ) < log (Real.sqrt (10 : ℝ)) := by
                apply Real.log_lt_log
                all_goals norm_num
                <;> nlinarith [Real.sqrt_nonneg (10 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num)]
              have h5 : log (Real.sqrt (10 : ℝ)) = (log (10 : ℝ) / 2 : ℝ) := by
                calc
                  log (Real.sqrt (10 : ℝ)) = log ((10 : ℝ) ^ (1 / 2 : ℝ)) := by
                    rw [Real.sqrt_eq_rpow]
                  _ = (1 / 2 : ℝ) * log (10 : ℝ) := by
                    rw [log_rpow]
                    all_goals linarith
                  _ = (log (10 : ℝ) / 2 : ℝ) := by
                    ring
              linarith [h4, h5]
            have h4 : logb (10 : ℝ) (3 : ℝ) = log (3 : ℝ) / log (10 : ℝ) := by
              field_simp [logb]
            rw [h4]
            have h5 : log (10 : ℝ) > 0 := by
              apply Real.log_pos
              all_goals norm_num
            apply (div_lt_iff₀ h5).mpr
            nlinarith [h3, Real.log_pos (show (10 : ℝ) > 1 by norm_num)]
          norm_num [h3_10] at *
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp
  <;> norm_num