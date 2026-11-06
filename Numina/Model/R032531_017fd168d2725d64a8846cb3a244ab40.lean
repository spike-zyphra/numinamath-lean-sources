import Mathlib

theorem number_theory_5313 (x y z : ℤ) (h : x^2 + y^2 = z^2) (h1 : x.gcd y = 1) :
    (Even x ∧ Odd y) ∨ (Odd x ∧ Even y) := by
  have h2 : (x % 2 = 0 ∨ x % 2 = 1) := by omega
  have h3 : (y % 2 = 0 ∨ y % 2 = 1) := by omega
  have h4 : (x % 2 = 0 ∧ y % 2 = 0) ∨ (x % 2 = 0 ∧ y % 2 = 1) ∨ (x % 2 = 1 ∧ y % 2 = 0) ∨ (x % 2 = 1 ∧ y % 2 = 1) := by
    tauto
  rcases h4 with h4 | h4 | h4 | h4
  · -- Assume both x and y are even.
    exfalso
    have h5 : (2 ∣ x) := by omega
    have h6 : (2 ∣ y) := by omega
    have h12 : (2) ∣ (x.gcd y : ℤ) := by
        apply Int.dvd_gcd h5 h6
    rw [h1] at h12
    omega
  · -- Assume x even, y odd.
    left
    constructor
    · -- Show that x is even.
      have h5 : x % 2 = 0 := h4.1
      exact ⟨x / 2, by omega⟩
    · -- Show that y is odd.
      have h6 : y % 2 = 1 := h4.2
      exact ⟨y / 2, by omega⟩
  · -- Assume x odd, y even.
    right
    constructor
    · -- Show that x is odd.
      have h7 : x % 2 = 1 := h4.1
      exact ⟨x / 2, by omega⟩
    · -- Show that y is even.
      have h8 : y % 2 = 0 := h4.2
      exact ⟨y / 2, by omega⟩
  · -- Assume both odd.
    exfalso
    have h5 : x % 2 = 1 := h4.1
    have h6 : y % 2 = 1 := h4.2
    have h7 : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by 
        omega
    have h8 : y % 8 = 1 ∨ y % 8 = 3 ∨ y % 8 = 5 ∨ y % 8 = 7 := by 
        omega
    have h9 : z^2 % 8 = 0 ∨ z^2 % 8 = 1 ∨ z^2 % 8 = 4 := by 
        have h4 : z % 8 = 0 ∨ z % 8 = 1 ∨ z % 8 = 2 ∨ z % 8 = 3 ∨ z % 8 = 4 ∨ z % 8 = 5 ∨ z % 8 = 6 ∨ z % 8 = 7 := by omega
        rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4) <;> simp [pow_two, h4, Int.add_emod, Int.mul_emod]
    have h10 : x^2 % 8 = 1 := by
        rcases h7 with (h7 | h7 | h7 | h7) <;> simp [pow_two, h7, Int.add_emod, Int.mul_emod]
    have h11 : y^2 % 8 = 1 := by
        rcases h8 with (h8 | h8 | h8 | h8) <;> simp [pow_two, h8, Int.add_emod, Int.mul_emod]
    have h12 : (x^2 + y^2) % 8 = 2 := by
        omega
    have h14 : (x^2 + y^2) % 8 = (z^2) % 8 := by 
        omega
    omega