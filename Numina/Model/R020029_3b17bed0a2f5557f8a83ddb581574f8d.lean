import Mathlib

open Real
open scoped BigOperators

theorem number_theory_52198 (h : ℕ → ℝ)
  (h_def : ∀ n, h n = ∑ i in Finset.Icc 1 n, (1 : ℝ)/i) :
  ∀ n ≥ 2, n + ∑ i in Finset.Icc 1 (n - 1), h i = n * h n := by 
  intro n hn
  have h11 : ∀ (n : ℕ), n ≥ 2 → n + ∑ i in Finset.Icc 1 (n - 1), h i = n * h n := by 
    intro n hn 
    have base2 : (2 : ℕ) + ∑ i in Finset.Icc 1 (2 - 1), h i = (2 : ℕ) * h 2 := by 
      have h1eq2 : h 1 = 1 := by rw [h_def 1]; norm_num [Finset.sum_Icc_succ_top]
      have h2eq3div2 : h 2 = 1 + 1 / 2 := by rw [h_def 2]; norm_num [Finset.sum_Icc_succ_top]
      norm_num [Finset.sum_Icc_succ_top,h1eq2,h2eq3div2,h_def] 
    have step1 : ∀ (k : ℕ), 2 ≤ k → 
      (k + ∑ i in Finset.Icc 1 (k - 1), h i = k * h k) → 
      ((k + 1 : ℕ) + (∑ i in Finset.Icc 1 ((k + 1 : ℕ) - 1), h i) = (k + 1 : ℕ) * h (k + 1)) := by 
      intro k hk h11_k
      have h5 : ∑ i in Finset.Icc 1 ((k + 1 : ℕ) - 1), h i = ∑ i in Finset.Icc 1 (k : ℕ), h i := by 
        rw [show (k + 1 - 1 : ℕ) = k by omega] 
      rw [h5] at *
      have h8 : (k : ℕ) ≥ 1 := by omega 
      have h15 : ∑ i in Finset.Icc 1 (k : ℕ), h i = ∑ i in Finset.Icc 1 (k - 1), h i + h k := by 
        rw [show (k : ℕ) = (k - 1) + 1 by omega] 
        rw [Finset.sum_Icc_succ_top (by omega)]
        <;> simp 
      rw [h15] at *
      have h_n1_eq : h (k + 1) = h k + (1 : ℝ) / (k + 1 : ℝ) := by 
        rw [h_def (k + 1), h_def k]
        simp [Finset.sum_Icc_succ_top, add_assoc]
        <;> ring 
      rw [h_n1_eq] at *
      all_goals
        cases k with 
        | zero => 
          exfalso 
          all_goals 
            omega 
        | succ k => 
          cases k with
          | zero => 
            simp [h_def] at h11_k ⊢ 
            all_goals norm_num [h_def] at h11_k ⊢
          | succ k => 
            simp [h_def] at h11_k ⊢ 
            all_goals 
              field_simp at h11_k ⊢ 
              <;> ring_nf at h11_k ⊢ 
              <;> norm_num at h11_k ⊢ 
              <;> linarith 
    exact Nat.le_induction base2 step1 n hn 
  specialize h11 n hn 
  simpa using h11