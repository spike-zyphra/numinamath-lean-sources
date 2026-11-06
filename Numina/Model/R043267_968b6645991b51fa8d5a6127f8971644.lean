import Mathlib

theorem number_theory_217100 (m n : ℕ) :
    ∃ k, k^2 = 2^n + 5 * 3^m ↔ (m, n) = (2, 2) := by
  use 7
  constructor
  · -- Assume k^2 = 2^n + 5 * 3^m; prove (m, n) = (2, 2)
    intro h
    have h1 : 2^n + 5 * 3^m = 49 := by
      have h2 : 7 ^ 2 = 49 := by norm_num
      linarith [h, h2]
    have h2 : m = 2 := by
      have h3 : m ≤ 4 := by
        by_contra h4
        push_neg at h4
        have h4' : 3 ^ m ≥ 3 ^ 5 := by
          have h5 : m ≥ 5 := by linarith
          exact Nat.pow_le_pow_of_le_right (by norm_num) h5
        have h4'' : 3 ^ m ≥ 243 := by
          norm_num at h4' ⊢
          linarith
        have h4''' : 2 ^ n ≥ 0 := by positivity
        linarith
      have h4 : n ≤ 10 := by 
        by_contra h5
        push_neg at h5
        have h6 : 2 ^ n ≥ 2 ^ 11 := by 
          have h7 : n ≥ 11 := by linarith
          exact Nat.pow_le_pow_of_le_right (by norm_num) h7
        have h8 : 2 ^ n ≥ 2048 := by 
          norm_num at h6 ⊢
          linarith
        interval_cases m <;> norm_num at h1 <;> linarith
      interval_cases m <;> interval_cases n <;> norm_num at h1 <;> tauto
    have h3 : n = 2 := by
      have h4 : 2 ^ n = 4 := by
        have h5 : 2 ^ n + 5 * 3 ^ m = 49 := by linarith [h1]
        rw [h2] at h5
        have h6 : 2 ^ n + 5 * 3 ^ 2 = 49 := by linarith [h5]
        norm_num at h6
        linarith
      have h7 : n = 2 := by
        have h8 : 2 ^ n = 4 := by linarith [h4]
        exact Nat.pow_right_injective (by norm_num) h8
      linarith
    simp [Prod.ext_iff, h2, h3]
  · -- Assume (m, n) = (2, 2); prove k^2 = 2^n + 5 * 3^m
    rintro h
    simp [Prod.mk.injEq] at h 
    rcases h with ⟨rfl, rfl⟩
    all_goals norm_num