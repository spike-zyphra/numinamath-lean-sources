import Mathlib

open Int

theorem number_theory_242607 (a : ℤ) :
    (∀ n : ℤ, 15 ∣ 10 * n^3 + 3 * n^5 + 7 * a * n) ↔ a % 15 = 11 := by
  constructor
  · -- Assume that for all n, 15 divides the expression. Prove that a ≡ 11 (mod 15)
    intro h
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    have h4 := h 4
    omega
  · -- Assume that a ≡ 11 (mod 15). Prove that 15 divides the expression for all n.
    intro h n
    have ha1 : a % 15 = 11 := h
    have h6 : (10 * n^3 + 3 * n^5 + 7 * a * n) % 15 = 0 := by
      have h7 : n % 15 = 0 ∨ n % 15 = 1 ∨ n % 15 = 2 ∨ n % 15 = 3 ∨ n % 15 = 4 ∨ n % 15 = 5 ∨ n % 15 = 6 ∨ n % 15 = 7 ∨ n % 15 = 8 ∨ n % 15 = 9 ∨ n % 15 = 10 ∨ n % 15 = 11 ∨ n % 15 = 12 ∨ n % 15 = 13 ∨ n % 15 = 14 := by 
        omega
      rcases h7 with (h7 | h7 | h7 | h7 | h7 | h7 | h7 | h7 | h7 | h7 | h7 | h7 | h7 | h7 | h7) <;> simp [Int.add_emod, Int.sub_emod, Int.mul_emod, pow_two, pow_succ, h7, 
          show a % 15 = 11 by omega] at *
      <;> omega
    exact Int.dvd_of_emod_eq_zero h6