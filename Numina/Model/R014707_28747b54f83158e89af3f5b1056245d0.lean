import Mathlib

theorem algebra_231088 {p q r : Polynomial ℝ} (hp : Irreducible p)
    (h : p ∣ q * r) : p ∣ q ∨ p ∣ r := by 
  have h1 : Prime p := by
    exact (irreducible_iff_prime).mp hp
  have h2 : p ∣ q ∨ p ∣ r := by
    apply Prime.dvd_or_dvd h1 h 
  exact h2