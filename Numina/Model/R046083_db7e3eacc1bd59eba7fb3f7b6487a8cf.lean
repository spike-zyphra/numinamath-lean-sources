import Mathlib

theorem number_theory_66383 (a b : ℕ) (_ : 0 < a) (hb : 0 < b)
    (hab : Nat.Coprime a b) :
    ∃ n : ℕ, 0 < n ∧ n ≤ b ∧ b ∣ a ^ n - 1 := by 
  use b.totient
  constructor
  · -- Show that $0 < b.totient$.
    have h1 : 0 < b.totient := by
      apply Nat.totient_pos.mpr
      omega 
    linarith
  constructor 
  · -- Show that $b.totient \le b$.
    have h2 : b.totient ≤ b := by 
      apply Nat.totient_le 
    omega
  · -- Show that $b$ divides $a ^ b.totient - 1$.
    have h4 : a ^ b.totient ≡ 1 [MOD b] := by 
      apply Nat.ModEq.pow_totient 
      exact hab 
    have h6 : b ∣ (a ^ b.totient - 1) := by 
      exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h4)
    exact h6