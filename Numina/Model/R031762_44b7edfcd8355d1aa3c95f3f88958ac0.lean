import Mathlib

theorem number_theory_126579 (x y : ℕ) :
    x > 0 ∧ y > 0 ∧ x^2 - 2 * Nat.factorial y = 2021 ↔ (x, y) = (45, 2) := by
  constructor
  · -- Assume h: x > 0 ∧ y > 0 ∧ x^2 - 2 * Nat.factorial y = 2021, prove (x, y) = (45, 2)
    rintro ⟨hx, hy, he⟩
    have h1 : x^2 = 2 * Nat.factorial y + 2021 := by 
      omega
    by_cases h2 : y ≤ 6
    · -- we can check y from 1 to 6 
      interval_cases y <;> norm_num [Nat.factorial] at h1 
        <;> try { 
          have h3 : x ≤ 159 := by
            nlinarith
          interval_cases x <;> norm_num at h1 <;> simp [Prod.ext_iff] 
        } 
        <;> omega
    · -- not y ≤ 6 which means y ≥ 7 
      have h3 : y ≥ 7 := by
        omega
      have h4 : 7 ∣ Nat.factorial y := by
        apply Nat.dvd_factorial
        all_goals
          linarith
      have h5 : (2 * Nat.factorial y) % 7 = 0 := by
        have h4' : 7 ∣ Nat.factorial y := h4
        have h8 : Nat.factorial y % 7 = 0 := by 
          exact Nat.dvd_iff_mod_eq_zero.mp h4'
        omega
      have h6 : x^2 % 7 = 0 ∨ x^2 % 7 = 1 ∨ x^2 % 7 = 2 ∨ x^2 % 7 = 4 := by 
        have h1 : x % 7 = 0 ∨ x % 7 = 1 ∨ x % 7 = 2 ∨ x % 7 = 3 ∨ x % 7 = 4 ∨ x % 7 = 5 ∨ x % 7 = 6 := by
          omega
        rcases h1 with (h | h | h | h | h | h | h) <;> simp [pow_two, Nat.mul_mod, h, Nat.mul_mod, Nat.mod_self]
      have h7 : (x^2) % 7 = 5 := by 
        have h8 : (2 * Nat.factorial y) % 7 = 0 := h5
        omega
      omega
  · -- Assume (x, y) = (45, 2) prove x > 0 ∧ y > 0 ∧ x^2 - 2 * Nat.factorial y = 2021
    rintro ⟨rfl, rfl⟩
    constructor
    · norm_num
    constructor
    · norm_num
    · -- Check that 45^2 - 2 * 2! = 2025 - 4 = 2021
      norm_num [Nat.factorial]