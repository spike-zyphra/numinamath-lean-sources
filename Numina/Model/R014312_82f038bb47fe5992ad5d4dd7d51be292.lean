import Mathlib

open Finset

theorem algebra_203069 {a : ℕ → ℝ}
    (ha : ∀ n ∈ Icc 1 5, a n = n)
    (h : ∀ n ≥ 5, a (n + 1) = ∏ i ∈ Icc 1 n, a i - 1) :
    IsGreatest {x | ∃ m, x = ∏ i ∈ Icc 1 m, a i - ∑ i ∈ Icc 1 m, (a i)^2} 65 := by
  constructor
  · -- Show 65 is in the set
    use 5
    norm_num [Finset.sum_Icc_succ_top, ha, Finset.prod_Icc_succ_top]
  · -- Show there is no greater element in the set
    intro x hx
    rcases hx with ⟨m, hm⟩
    by_contra h1
    push_neg at h1
    have eq1 : ∏ i ∈ Icc 1 m, a i - ∑ i ∈ Icc 1 m, (a i)^2 > (65 : ℝ) := by
      linarith [h1, hm]
    by_cases h2 : m ≤ 5
    · 
      interval_cases m <;> norm_num [Finset.sum_Icc_succ_top, ha, Finset.prod_Icc_succ_top] at eq1 
    · -- m > 5
      have h3 : m ≥ 6 := by
        omega 
      have eq2 : ∏ i ∈ Icc 1 m, a i - ∑ i ∈ Icc 1 m, (a i) ^ 2 ≤ (64 : ℝ) := by
        have h5 : ∀ (n : ℕ), n ≥ 6 → ∏ i ∈ Icc 1 n, a i - ∑ i ∈ Icc 1 n, (a i) ^ 2 ≤ (64 : ℝ) := by
          intro n hn
          have h11 : n ≥ 6 := by linarith 
          have eq3 : a 6 = ∏ i ∈ Icc 1 5, a i - 1 := h 5 (by linarith)
          norm_num [Finset.prod_Icc_succ_top, ha] at eq3 
          have base6 : ∏ i ∈ Icc 1 6, a i - ∑ i ∈ Icc 1 6, (a i) ^ 2 ≤ (64 : ℝ) := by 
            norm_num [Finset.prod_Icc_succ_top, Finset.sum_Icc_succ_top, ha, eq3]
          have step : ∀ (k : ℕ), k ≥ 6 → ∏ i ∈ Icc 1 k, a i - ∑ i ∈ Icc 1 k, (a i) ^ 2 ≤ (64 : ℝ) → ∏ i ∈ Icc 1 (k + 1), a i - ∑ i ∈ Icc 1 (k + 1), (a i) ^ 2 ≤ (64 : ℝ) := by
            intro k hk h14
            have eq4 : a (k + 1) = ∏ i ∈ Icc 1 k, a i - 1 := by
              apply h 
              linarith 
            have eq5 : ∏ i ∈ Icc 1 (k + 1), a i = (∏ i ∈ Icc 1 k, a i) * a (k + 1) := by 
              simp [prod_Icc_succ_top, mul_comm]
            have eq6 : ∑ i ∈ Icc 1 (k + 1), (a i) ^ 2 = ∑ i ∈ Icc 1 k, (a i) ^ 2 + (a (k + 1)) ^ 2 := by 
              rw [sum_Icc_succ_top (by linarith)]
            rw [eq5, eq6]
            nlinarith [sq_nonneg (∏ i ∈ Icc 1 k, a i), sq_nonneg (a (k + 1)), sq_nonneg (a (k + 1) - (∏ i ∈ Icc 1 k, a i)), sq_nonneg (a 1 - 1), sq_nonneg (a 2 - 2), sq_nonneg (a 3 - 3), sq_nonneg (a 4 - 4), sq_nonneg (a 5 - 5), 
                      ha 1 (by simp), ha 2 (by simp), ha 3 (by simp), ha 4 (by simp), ha 5 (by simp)]
          exact Nat.le_induction base6 step n (by linarith)
        specialize h5 m (by linarith)
        simpa using h5 
      linarith [eq1, eq2]