import Mathlib


theorem number_theory_301212 :
    IsLeast {n : ℕ | ∃ a b : ℕ, a > 0 ∧ b > 0 ∧ n = (15 * a + 16 * b)^2 ∧ ∃ m : ℕ, m > 0 ∧ n = (16 * a - 15 * b)^2} (481^2) := by 
  constructor 
  · -- Show that 481^2 is in the set 
    use 31, 1 
    all_goals 
      constructor 
      · norm_num -- a > 0 
      constructor 
      · norm_num -- b > 0 
      constructor 
      · norm_num -- n = (15 * a + 16 * b)^2 
      use 31 
      all_goals 
        norm_num -- m > 0 ∧ n = (16 * a - 15 * b)^2 
  · -- Show that 481^2 is the smallest 
    intro n hn 
    rcases hn with ⟨a, b, ha, hb, hn1, m, hm, hn2⟩ 
    by_contra h 
    push_neg at h 
    have h_eq_n : (15 * a + 16 * b : ℕ) ^ 2 = (16 * a - 15 * b : ℕ) ^ 2 := by 
      nlinarith [hn1, hn2]
    have heq2 : (15 * a + 16 * b : ℕ) = (16 * a - 15 * b : ℕ) := by 
      have heq2 : (15 * a + 16 * b : ℕ) ^ 2 = (16 * a - 15 * b : ℕ) ^ 2 := h_eq_n 
      have h15 : (15 * a + 16 * b : ℕ) ≥ 0 := by positivity 
      have h16 : (16 * a - 15 * b : ℕ) ≥ 0 := by positivity 
      have heq3 : (15 * a + 16 * b : ℕ) = (16 * a - 15 * b : ℕ) := by 
        nlinarith [sq_nonneg ((15 * a + 16 * b : ℕ) : ℕ), sq_nonneg ((16 * a - 15 * b : ℕ) : ℕ)]
      exact heq3 
    have heq3 : a = 31 * b := by 
      omega 
    have heq4 : n = (481 * b) ^ 2 := by
      have heq5 : (15 * a + 16 * b : ℕ) = (481 * b) := by
        nlinarith [heq3]
      nlinarith [hn1, heq5]
    have heq5 : b < 1 := by
      nlinarith [heq4, h]
    have heq6 : b ≥ 1 := by 
      omega 
    linarith