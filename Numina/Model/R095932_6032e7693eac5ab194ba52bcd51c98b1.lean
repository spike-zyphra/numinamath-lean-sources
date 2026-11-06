import Mathlib

theorem number_theory_212605 (a : ℕ) (ha : a > 0) (k : ℕ) :
    k > 0 → (a + k - 1) ^ 2 ≠ (a + k) ^ 2 ∧
    (a + k - 1) ^ 2 ≠ (a + k + 1) ^ 2 ∧
    (a + k) ^ 2 ≠ (a + k + 1) ^ 2 := by 
  intro hk
  have h1 : (a + k - 1) ^ 2 ≠ (a + k) ^ 2 := by 
    by_contra h
    have h2 : a + k - 1 < a + k := by 
      omega
    have h3 : (a + k - 1) ^ 2 < (a + k) ^ 2 := by 
      apply Nat.pow_lt_pow_left
      all_goals omega
    linarith
  have h2 : (a + k - 1) ^ 2 ≠ (a + k + 1) ^ 2 := by 
    by_contra h
    have h4 : (a + k - 1) ^ 2 < (a + k + 1) ^ 2 := by 
      have h5 : a + k - 1 < a + k + 1 := by 
        omega
      apply Nat.pow_lt_pow_left
      all_goals omega
    linarith
  have h3 : (a + k) ^ 2 ≠ (a + k + 1) ^ 2 := by 
    by_contra h
    have h6 : (a + k) ^ 2 < (a + k + 1) ^ 2 := by 
      have h7 : a + k < a + k + 1 := by 
        omega
      apply Nat.pow_lt_pow_left
      all_goals omega
    linarith
  exact ⟨h1, h2, h3⟩