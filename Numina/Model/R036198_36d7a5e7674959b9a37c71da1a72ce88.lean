import Mathlib

theorem number_theory_97476 {n : ℕ} (hn : n > 0) (h1 : Nat.digits 14 n = [c, b, a])
    (h2 : Nat.digits 15 n = [b, c, a]) (h3 : Nat.digits 6 n = [c, a, c, a]) :
    n = 925 := by

  have h1' : n = a * 14^2 + b * 14 + c := by 
    rw [← Nat.ofDigits_digits 14 n]
    rw [h1]
    simp [Nat.ofDigits, mul_add, mul_one]
    <;> ring

  have h2' : n = a * 15^2 + c * 15 + b := by 
    rw [← Nat.ofDigits_digits 15 n]
    rw [h2]
    simp [Nat.ofDigits, mul_add, mul_one]
    <;> ring

  have h3' : n = a * 6^3 + c * 6^2 + a * 6 + c := by
    rw [← Nat.ofDigits_digits 6 n]
    rw [h3]
    simp [Nat.ofDigits, mul_add, mul_one]
    <;> ring

  have h4 : a = 4 * c := by
    omega

  have h5 : b = 10 * c := by 
    omega

  have h6 : c = 1 := by 
    have h7 : c < 6 := by
      have hc : Nat.digits 6 n = [c, a, c, a] := h3
      have h9 : c ∈ Nat.digits 6 n := by
        rw [hc]
        simp
      exact Nat.digits_lt_base (by norm_num) h9
    have h8 : b < 14 := by
      have h9 : Nat.digits 14 n = [c, b, a] := h1
      have h9' : b ∈ Nat.digits 14 n := by
        rw [h9]
        simp
      have h9'' : b < 14 := by
        exact Nat.digits_lt_base (by norm_num) h9'
      omega
    rw [show b = 10 * c by omega] at h8
    omega

  have ha : a = 4 := by
    omega

  have hb : b = 10 := by
    omega

  have hn1 : n = 925 := by
    rw [h3']
    rw [ha, h6]
    all_goals norm_num

  exact hn1