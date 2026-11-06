import Mathlib

theorem number_theory_78830 (a : ℤ) (ha : Odd a) :
    ∃ x y z, a^4 + 4*a^3 + 11*a^2 + 6*a + 2 = x^2 + y^2 + z^2 ∧ 4 ∣ a^4 + 4*a^3 + 11*a^2 + 6*a + 2 := by
  use a^2 + 2*a + 1 
  use a + 1 
  use 2*a 
  constructor 
  · -- Show that a^4 + 4*a^3 + 11*a^2 + 6*a + 2 = x^2 + y^2 + z^2
    ring
  · -- Show that 4 divides a^4 + 4*a^3 + 11*a^2 + 6*a + 2
    have ha1 : a % 4 = 1 ∨ a % 4 = 3 := by 
      have h1 : a % 2 = 1 := by 
        obtain ⟨k, hk⟩ := ha
        omega 
      omega 
    rcases ha1 with (h | h)
    · -- Case a % 4 = 1 
      have h2 : (a ^ 4 + 4 * a ^ 3 + 11 * a ^ 2 + 6 * a + 2) % 4 = 0 := by 
        simp [h, pow_succ, Int.add_emod, Int.mul_emod]
        <;> omega 
      omega 
    · -- Case a % 4 = 3 
      have h2 : (a ^ 4 + 4 * a ^ 3 + 11 * a ^ 2 + 6 * a + 2) % 4 = 0 := by 
        simp [h, pow_succ, Int.add_emod, Int.mul_emod]
        <;> omega 
      omega