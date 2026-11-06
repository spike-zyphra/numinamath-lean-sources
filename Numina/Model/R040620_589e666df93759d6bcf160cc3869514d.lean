import Mathlib

theorem number_theory_288596 (a b : ℕ) (ha : a > 0) (hb : b > 0)
    (h1 : a % b = 0) (h2 : b ≠ 0) :
    ∃ x, x > b ∧ x % b = 0 ∧ x % a = 0 := by 
  by_cases h3 : a > b
  · -- If a > b, then use a = x. Note that from h1 and h3, a is a multiple of b and a > b
    use a
    constructor
    · exact h3
    constructor
    · exact h1
    · simp
  · -- If a ≤ b
    have h3 : b ∣ a := Nat.dvd_of_mod_eq_zero h1
    have h4 : a = b := by 
      have h4 : a ≤ b := by 
          omega
      have h5 : a ≥ b := by
        exact Nat.le_of_dvd (by linarith) h3
      linarith
    use 2*a
    constructor
    · -- Show that 2*a > b
      rw [show b = a by linarith [h4]]
      nlinarith [ha]
    constructor
    · -- Show that (2*a) % b = 0
      rw [show b = a by linarith [h4]]
      simp [Nat.mul_mod, Nat.mod_self]
    · -- Show that (2*a) % a = 0
      simp [Nat.mul_mod, Nat.mod_self]