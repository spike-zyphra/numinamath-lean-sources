import Mathlib

theorem number_theory_6884 (a b c : ℕ) (_ : 0 < a) (h1 : 0 < b) (h2 : 0 < c)
    (h3 : Nat.gcd a b = 1) (h4 : a ∣ b * c) : a ∣ c := by 
  exact Nat.Coprime.dvd_of_dvd_mul_left h3 h4