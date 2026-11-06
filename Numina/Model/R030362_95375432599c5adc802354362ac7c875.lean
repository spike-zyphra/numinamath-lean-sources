import Mathlib

theorem algebra_466 : IsGreatest {p : ℕ | ∃ m n : ℕ, p ≠ 0 ∧ n ≠ 0 ∧ m ≠ 0 ∧ m ≥ n ∧ n ≥ p ∧ (m - 8 / 3 : ℝ) * (n - 8 / 3 : ℝ) * (p - 8 / 3 : ℝ) = m * n * p / 27} 4 := by
  constructor 
  · -- Show 4 is in the set.
    use 4, 4 
    norm_num 
  · -- Show 4 is greatest in the set
    intro p hp
    rcases hp with ⟨m, n, hp_nz, hn_nz, hm_nz, hmge, hnge, heq⟩
    by_contra h 
    push_neg at h 
    have hp5 : p ≥ 5 := by 
      omega 
    have eq1 : (m : ℝ) ≥ (n : ℝ) := by exact_mod_cast hmge 
    have eq2 : (n : ℝ) ≥ (p : ℝ) := by exact_mod_cast hnge 
    have eq3 : (m : ℝ) ≥ (p : ℝ) := by linarith 
    have eq5 : (3 * (m : ℝ) - 8) * (3 * (n : ℝ) - 8) * (3 * (p : ℝ) - 8) = (m : ℝ) * (n : ℝ) * (p : ℝ) := by 
      nlinarith 
    have eq6 : (3 * m - 8 : ℤ) * (3 * n - 8 : ℤ) * (3 * p - 8 : ℤ) = (m * n * p : ℤ) := by 
      exact_mod_cast eq5 
    have hm5 : m ≥ 5 := by
      omega 
    have hn5 : n ≥ 5 := by
      omega 
    -- from eq6, we get m, n, p bounded.
    have h9 : m ≤ 24 := by
      nlinarith [sq_nonneg ((m : ℤ) - 5 : ℤ), sq_nonneg ((n : ℤ) - 5 : ℤ), sq_nonneg ((p : ℤ) - 5 : ℤ),
                  mul_nonneg (show (0 : ℤ) ≤ (m : ℤ) by omega) (show (0 : ℤ) ≤ (n : ℤ) by omega), 
                  mul_nonneg (show (0 : ℤ) ≤ (n : ℤ) by omega) (show (0 : ℤ) ≤ (p : ℤ) by omega),
                  mul_nonneg (show (0 : ℤ) ≤ (m : ℤ) by omega) (show (0 : ℤ) ≤ (p : ℤ) by omega)
                 ]
    have h11 : n ≤ 24 := by 
      nlinarith [sq_nonneg ((m : ℤ) - 5 : ℤ), sq_nonneg ((n : ℤ) - 5 : ℤ), sq_nonneg ((p : ℤ) - 5 : ℤ),
                  mul_nonneg (show (0 : ℤ) ≤ (m : ℤ) by omega) (show (0 : ℤ) ≤ (n : ℤ) by omega), 
                  mul_nonneg (show (0 : ℤ) ≤ (n : ℤ) by omega) (show (0 : ℤ) ≤ (p : ℤ) by omega),
                  mul_nonneg (show (0 : ℤ) ≤ (m : ℤ) by omega) (show (0 : ℤ) ≤ (p : ℤ) by omega)
                 ]
    have h12 : p ≤ 24 := by 
      nlinarith [sq_nonneg ((m : ℤ) - 5 : ℤ), sq_nonneg ((n : ℤ) - 5 : ℤ), sq_nonneg ((p : ℤ) - 5 : ℤ),
                  mul_nonneg (show (0 : ℤ) ≤ (m : ℤ) by omega) (show (0 : ℤ) ≤ (n : ℤ) by omega), 
                  mul_nonneg (show (0 : ℤ) ≤ (n : ℤ) by omega) (show (0 : ℤ) ≤ (p : ℤ) by omega),
                  mul_nonneg (show (0 : ℤ) ≤ (m : ℤ) by omega) (show (0 : ℤ) ≤ (p : ℤ) by omega)
                 ]
    interval_cases p <;> interval_cases n <;> omega