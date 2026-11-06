import Mathlib

theorem algebra_146608 (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (h : a * b + 2 = a^3 + 2 * b) :
    (a = 1 ∧ b = 1) ∨ (a = 3 ∧ b = 25) ∨ (a = 4 ∧ b = 31) ∨
    (a = 5 ∧ b = 41) ∨ (a = 8 ∧ b = 85) := by 
  have eq : a ≤ 8 := by
    by_contra h2
    push_neg at h2
    have eq1 : b ≤ a ^ 2 + 2 * a + 4 := by
      nlinarith [sq_nonneg ((a : ℕ) : ℕ), sq_nonneg ((b : ℕ) : ℕ), sq_pos_of_pos ha, sq_pos_of_pos hb]
    have eq2 : b ≥ a ^ 2 + 2 * a + 4 := by
      nlinarith [sq_nonneg ((a : ℕ) : ℕ), sq_nonneg ((b : ℕ) : ℕ), sq_pos_of_pos ha, sq_pos_of_pos hb, 
        sq_nonneg ((a : ℕ) : ℕ), sq_nonneg ((b - a ^ 2 : ℤ) : ℤ)]
    have eq3 : b = a ^ 2 + 2 * a + 4 := by 
      omega
    rw [show b = a ^ 2 + 2 * a + 4 by linarith [eq3]] at h
    nlinarith [sq_nonneg ((a : ℕ) : ℕ), sq_nonneg ((a ^ 2 : ℕ) : ℕ), sq_pos_of_pos ha, sq_pos_of_pos hb]
  interval_cases a <;> try { 
    omega 
  } <;> try { 
    have h5 : b ≤ 85 := by
      nlinarith 
    interval_cases b <;> omega
  }