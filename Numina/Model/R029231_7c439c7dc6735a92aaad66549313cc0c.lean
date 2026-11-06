import Mathlib

theorem number_theory_110958 (p : ℕ) (hp : p.Prime) :
    ∀ x y, x * y ≡ 0 [ZMOD p] → x ≡ 0 [ZMOD p] ∨ y ≡ 0 [ZMOD p] := by
  intro x y h
  have h1 : (p : Int) ∣ x * y := by
    exact Int.dvd_of_emod_eq_zero h

  have hp' : Prime (p : Int) := by 
    exact Int.prime_iff_natAbs_prime.mpr hp
  have h2 : (p : Int) ∣ x ∨ (p : Int) ∣ y := by
    apply hp'.dvd_or_dvd
    exact h1
  
  rcases h2 with h2 | h2
  · -- Assume p divides x, then x % p = 0
    left
    exact Int.emod_eq_zero_of_dvd h2
  · -- Assume p divides y, then y % p = 0
    right
    exact Int.emod_eq_zero_of_dvd h2