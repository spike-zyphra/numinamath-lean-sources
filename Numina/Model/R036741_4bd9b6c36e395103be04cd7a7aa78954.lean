import Mathlib

theorem number_theory_119089 (n : ℕ) (h : n > 0) (h1 : Nat.digits 5 n = [a, b, c])
    (h2 : a < b ∧ b < c) (h3 : n = 5 * a + b + c) :
    n = 108 := by
  have h4 : n = a + 5 * b + 25 * c := by
    rw [← Nat.ofDigits_digits 5 n]
    rw [h1]
    simp [Nat.ofDigits, mul_add, mul_comm]
    <;> all_goals omega

  -- now equate the two expressions
  have h5 : a + 5 * b + 25 * c = 5 * a + b + c := by
    omega

  -- simplifying gives
  have h6 : a = b + 6 * c := by
    omega

  -- constraints from base 5
  have h7 : a < 5 := by
    have h8 : a ∈ Nat.digits 5 n := by
      simp [h1]
    have h9 : a < 5 := by
      exact Nat.digits_lt_base (by norm_num) h8
    linarith [h9]

  -- constraints from base 5
  have h8 : b < 5 := by
    have h8 : b ∈ Nat.digits 5 n := by
      simp [h1]
    have h9 : b < 5 := by
      exact Nat.digits_lt_base (by norm_num) h8
    linarith [h9]

  -- constraints from base 5
  have h9 : c < 5 := by
    have h8 : c ∈ Nat.digits 5 n := by
      simp [h1]
    have h9 : c < 5 := by
      exact Nat.digits_lt_base (by norm_num) h8
    linarith [h9]

  -- From a = b + 6*c and a > 0
  have h10 : b + 6 * c < 5 := by
    nlinarith [h6, h7]

  -- Let's find possible solutions
  interval_cases c <;> interval_cases b
    <;> try { 
      omega 
    } <;> try { 
      exfalso 
      <;> try { 
        nlinarith 
      } <;> try { 
        tauto 
      }
    }
    <;> all_goals omega