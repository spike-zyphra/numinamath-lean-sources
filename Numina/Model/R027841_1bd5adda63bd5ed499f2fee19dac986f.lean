import Mathlib

theorem number_theory_223367 (n : ℕ) (h : n < 1000) (h' : Nat.digits 7 n = [a, b, c]) (h'' : Nat.digits 9 n = [c, b, a]) :
    n = 248 := by
  have eq1 : n = a + 7 * b + 49 * c := by 
    rw [← Nat.ofDigits_digits 7 n]
    rw [h']
    simp [Nat.ofDigits, mul_add, mul_one]
    all_goals omega
  have eq2 : n = c + 9 * b + 81 * a := by 
    rw [← Nat.ofDigits_digits 9 n]
    rw [h'']
    simp [Nat.ofDigits, mul_add, mul_one]
    all_goals omega
  have ha1 : a < 7 := by 
    have h5 : a ∈ Nat.digits 7 n := by 
      rw [h']
      simp 
    have h5' : a < 7 := by 
      exact Nat.digits_lt_base (by norm_num) h5
    linarith 
  have hb1 : b < 7 := by 
    have h5 : b ∈ Nat.digits 7 n := by 
      rw [h']
      simp 
    have h6 : b < 7 := by 
      exact Nat.digits_lt_base (by norm_num) h5 
    linarith
  have hc1 : c < 7 := by 
    have h5 : c ∈ Nat.digits 7 n := by 
      rw [h']
      simp 
    have h7 : c < 7 := by 
      exact Nat.digits_lt_base (by norm_num) h5 
    linarith 
  have ha2 : a < 9 := by 
    have h8 : a ∈ Nat.digits 9 n := by 
      rw [h'']
      simp 
    have h9 : a < 9 := by 
      exact Nat.digits_lt_base (by norm_num) h8 
    linarith 
  have hb2 : b < 9 := by 
    have h8 : b ∈ Nat.digits 9 n := by 
      rw [h'']
      simp 
    have h11 : b < 9 := by 
      exact Nat.digits_lt_base (by norm_num) h8 
    linarith
  have hc2 : c < 9 := by 
    have h8 : c ∈ Nat.digits 9 n := by 
      rw [h'']
      simp 
    have h13 : c < 9 := by 
      exact Nat.digits_lt_base (by norm_num) h8 
    linarith 
  interval_cases a <;> interval_cases b <;> interval_cases c 
    <;> norm_num [eq1, eq2] at h' h'' ⊢ 
    <;> try { contradiction }
    <;> omega