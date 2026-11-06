import Mathlib

theorem number_theory_288769 {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : ∃ d, d ∣ a ∧ d ∣ b) :
    IsGreatest {x | x ∣ a ∧ x ∣ b} (Nat.gcd a b) ∧ ∀ d, d ∣ a → d ∣ b → d ∣ Nat.gcd a b := by
  constructor
  · -- Show that `gcd a b` is greatest among all common divisors.
    constructor
    · -- Show that `gcd a b` is a common divisor.
      constructor
      · exact Nat.gcd_dvd_left a b
      · exact Nat.gcd_dvd_right a b
    · -- Show that `gcd a b` is greatest.
      intro x hx
      rcases hx with ⟨hx1, hx2⟩
      have h3 : x ∣ Nat.gcd a b := by
        exact Nat.dvd_gcd hx1 hx2
      have h4 : x ≤ Nat.gcd a b := by
        exact Nat.le_of_dvd (show 0 < Nat.gcd a b by
          have h9 : Nat.gcd a b > 0 := by
            apply Nat.gcd_pos_of_pos_left
            linarith
          linarith
        ) h3
      linarith
  · -- Show that any common divisor divides `gcd a b`.
    intro d ha1 ha2
    exact Nat.dvd_gcd ha1 ha2