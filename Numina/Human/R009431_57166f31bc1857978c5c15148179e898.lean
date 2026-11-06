import Mathlib

/- What is the largest divisor of 342 that is also a factor of 285? -/
theorem algebra_17088 : IsGreatest {x | x ∣ 342 ∧ x ∣ 285} 57 := by 
  refine' ⟨⟨Nat.dvd_of_mod_eq_zero rfl, Nat.dvd_of_mod_eq_zero rfl⟩, fun x hx => _⟩
  have h1 : x ∣ 342 := hx.1
  have h2 : x ∣ 285 := hx.2
  have h3 : x ∣ 57 := Nat.dvd_gcd h1 h2
  have h4 : 57 ∣ 57 := Nat.dvd_refl 57
  exact Nat.le_of_dvd (by decide) h3