import Mathlib

theorem number_theory_304463 (n : ℤ) :
    (n^2 + 1) ∣ (70 * n + 200) ↔ n = 0 ∨ n = 1 ∨ n = -1 ∨ n = 2 ∨ n = -2 ∨ n = 3 ∨ n = -3 ∨ n = -67 := by
  constructor
  · -- Assume (n^2 + 1) ∣ (70 * n + 200), prove the disjunction
    intro h
    rcases h with ⟨k, hk⟩
    have h1 : k * (n ^ 2 + 1) = 70 * n + 200 := by linarith
    by_cases h3 : n ≤ 100
    · -- Case n ≤ 100
      have h4 : n ≥ -100 := by
        by_contra h4
        push_neg at h4
        have h5 : n ≤ -101 := by nlinarith
        have h6 : n < -100 := h4
        have h7 : k ≤ 2 := by
          nlinarith [sq_nonneg (n + 70), sq_nonneg (k), sq_nonneg (k - 2), sq_nonneg (n + 3)]
        have h8 : k ≥ -4 := by
          nlinarith [sq_nonneg (n + 70), sq_nonneg (k), sq_nonneg (n + 3), sq_nonneg (k - 2)]
        interval_cases k <;> try { 
          nlinarith 
        }
      interval_cases n <;> norm_num at h1 ⊢ <;> omega
    · -- Case n > 100
      have h4 : n ≥ 101 := by 
        omega
      have h8 : k ≤ 2 := by
        nlinarith [sq_nonneg (n - 70), sq_nonneg (k), sq_nonneg (k - 2), sq_nonneg (n - 1)]
      have h9 : k ≥ 1 := by
        nlinarith [sq_nonneg (n - 70), sq_nonneg (k), sq_nonneg (n - 1), sq_nonneg (n ^ 2 - 1)]
      interval_cases k <;> try { 
        nlinarith 
      }
  · -- Show that for each of the listed values of n, (n^2 + 1) divides (70 * n + 200)
    rintro (h | h | h | h | h | h | h | h)
    · -- n = 0
      rw [h]
      norm_num
    · -- n = 1
      rw [h]
      norm_num
    · -- n = -1
      rw [h]
      norm_num
    · -- n = 2
      rw [h]
      norm_num
    · -- n = -2
      rw [h]
      norm_num
    · -- n = 3
      rw [h]
      norm_num
    · -- n = -3
      rw [h]
      norm_num
    · -- n = -67
      rw [h]
      norm_num