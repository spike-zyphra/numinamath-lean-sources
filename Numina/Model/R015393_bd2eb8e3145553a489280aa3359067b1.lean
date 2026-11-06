import Mathlib

theorem number_theory_193327 {a b c : ℕ} (hab : a.gcd b = 1) (hdiv : a ∣ b * c) :
    a ∣ c := by 
  have h1 : a.Coprime b := by 
    rw [Nat.coprime_iff_gcd_eq_one] 
    exact hab 
  exact Nat.Coprime.dvd_of_dvd_mul_left h1 hdiv