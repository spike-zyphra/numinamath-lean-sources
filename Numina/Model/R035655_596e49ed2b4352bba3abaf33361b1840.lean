import Mathlib

open Real

theorem algebra_190851 (n : ℕ) :
    ∑ k in Finset.Icc 1 n, ⌊(sqrt k + sqrt (k + 1))^2⌋ = n * (2 * n + 3) := by

  have h1 : ∀ (k : ℕ), k ≥ 1 → ⌊(sqrt k + sqrt (k + 1))^2⌋ = 4 * k + 1 := by
    intro k hk
    have h3 : (sqrt k + sqrt (k + 1)) ^ 2 = (2 * k + 1 : ℝ) + 2 * sqrt k * sqrt (k + 1) := by
      nlinarith [Real.sqrt_nonneg (k : ℝ), Real.sqrt_nonneg ((k + 1 : ℝ)), Real.sq_sqrt (show (k : ℝ) ≥ 0 by linarith), Real.sq_sqrt (show (k + 1 : ℝ) ≥ 0 by linarith)]
    have h4 : (sqrt k + sqrt (k + 1)) ^ 2 < (4 * k + 2 : ℝ) := by
      have h9 : sqrt k * sqrt (k + 1) < (k + 1/2 : ℝ) := by
        have h115 : (sqrt k * sqrt (k + 1)) ^ 2 < (k + 1/2 : ℝ) ^ 2 := by
          have h112 : (sqrt k * sqrt (k + 1)) ^ 2 = (k : ℝ) * (k + 1 : ℝ) := by
            calc
              (sqrt k * sqrt (k + 1)) ^ 2 = (sqrt k) ^ 2 * (sqrt (k + 1)) ^ 2 := by ring
              _ = (k : ℝ) * (k + 1 : ℝ) := by
                rw [Real.sq_sqrt, Real.sq_sqrt]
                all_goals
                  have : (k : ℝ) ≥ 0 := by exact_mod_cast show k ≥ (0 : ℕ) by omega
                  all_goals nlinarith
          rw [h112]
          nlinarith
        have h18 : sqrt k * sqrt (k + 1) ≥ 0 := by
          positivity
        have h101 : (k + 1/2 : ℝ) ≥ 0 := by
          positivity
        nlinarith [Real.sqrt_nonneg (k : ℝ), Real.sqrt_nonneg (k + 1 : ℝ)]
      have h19 : (2 * k + 1 : ℝ) + 2 * sqrt k * sqrt (k + 1) < (4 * k + 2 : ℝ) := by
        nlinarith
      nlinarith [Real.sqrt_nonneg (k : ℝ), Real.sqrt_nonneg (k + 1 : ℝ)]
    have h10 : (4 * k + 1 : ℝ) ≤ (sqrt k + sqrt (k + 1)) ^ 2 := by
      have h11 : sqrt k * sqrt (k + 1) ≥ (k : ℝ) := by
        have h115 : (sqrt k * sqrt (k + 1)) ≥ (k : ℝ) := by
          have h112 : (sqrt k * sqrt (k + 1)) ^ 2 ≥ (k : ℝ) ^ 2 := by
            have h114 : (sqrt k * sqrt (k + 1)) ^ 2 = (k : ℝ) * (k + 1 : ℝ) := by
              calc
                (sqrt k * sqrt (k + 1)) ^ 2 = (sqrt k) ^ 2 * (sqrt (k + 1)) ^ 2 := by ring
                _ = (k : ℝ) * (k + 1 : ℝ) := by
                  rw [Real.sq_sqrt, Real.sq_sqrt]
                  all_goals
                    have : (k : ℝ) ≥ 0 := by exact_mod_cast show k ≥ (0 : ℕ) by omega
                    all_goals nlinarith
            rw [h114]
            nlinarith
          have h101 : sqrt k * sqrt (k + 1) ≥ 0 := by
            positivity
          have h1010 : (k : ℝ) ≥ 0 := by
            positivity
          nlinarith
        linarith
      nlinarith [Real.sqrt_nonneg (k : ℝ), Real.sqrt_nonneg (k + 1 : ℝ), Real.sq_sqrt (show (k : ℝ) ≥ 0 by linarith), Real.sq_sqrt (show (k + 1 : ℝ) ≥ 0 by linarith)]
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> (try nlinarith)
  
  have h7 : ∑ k in Finset.Icc 1 n, ⌊(sqrt k + sqrt (k + 1))^2⌋ = ∑ k in Finset.Icc 1 n, (4 * k + 1 : ℤ) := by
    apply Finset.sum_congr
    · rfl
    · intro k hk
      have hk10 : k ≥ 1 := by
        have h15 : k ∈ Finset.Icc (1 : ℕ) n := by
          exact hk
        simp at h15 ⊢
        omega
      have h14 : ⌊(sqrt k + sqrt (k + 1))^2⌋ = (4 * k + 1 : ℤ) := by
        have hk15 : k ≥ 1 := hk10
        have h144 : ⌊(sqrt k + sqrt (k + 1))^2⌋ = 4 * k + 1 := h1 k hk15
        norm_num at h144 ⊢
        all_goals linarith
      simpa using h14

  rw [h7]
  have h310 : ∑ k in Finset.Icc 1 n, (4 * k + 1 : ℤ) = (n * (2 * n + 3) : ℤ) := by
    have h31 : ∀ (n : ℕ), ∑ k in Finset.Icc 1 n, (4 * k + 1 : ℤ) = (n * (2 * n + 3) : ℤ) := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [Finset.sum_Icc_succ_top (by linarith)]
        rw [ih]
        all_goals simp [mul_add, add_mul]
        all_goals ring
    specialize h31 n
    simpa using h31
  rw [h310]
  all_goals norm_cast