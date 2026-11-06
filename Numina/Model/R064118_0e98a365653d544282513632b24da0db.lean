import Mathlib

theorem number_theory_278773 (m : ℤ) (h : Even m) : 48 ∣ m^3 + 20 * m := by 
  rcases h with ⟨k, hk⟩
  have h1 : m^3 + 20 * m = 8 * (k^3 + 5 * k) := by 
    rw [hk]
    ring
  rw [h1]
  have h2 : (k^3 + 5 * k) % 2 = 0 := by
    have h3 : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases h3 with (h3 | h3)
    · 
      simp [pow_succ, Int.add_emod, Int.mul_emod, h3]
    · 
      simp [pow_succ, Int.add_emod, Int.mul_emod, h3]
  have h3 : (k^3 + 5 * k) % 3 = 0 := by
    have h4 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases h4 with (h4 | h4 | h4)
    · 
      simp [pow_succ, Int.add_emod, Int.mul_emod, h4]
    · 
      simp [pow_succ, Int.add_emod, Int.mul_emod, h4]
    · 
      simp [pow_succ, Int.add_emod, Int.mul_emod, h4]
  have : (k^3 + 5 * k) % 6 = 0 := by
    omega
  omega