import Mathlib

theorem number_theory_242512 (a : ℤ) :
    (∀ n : ℤ, 15 ∣ 5 * n^3 + 6 * n^5 + 4 * a * n) ↔ a % 15 = 1 := by 
  constructor
  · -- First direction: ∀ n, 15 ∣ 5n³+6n⁵+4an, then a % 15 = 1
    intro h
    have h1 := h 1
    norm_num at h1 
    have h2 : a % 15 = 1 := by 
      omega 
    assumption
  · -- Second direction: a % 15 = 1, then ∀ n, 15 ∣ 5n³+6n⁵+4an.
    intro h
    intro n 
    have h1 : a % 15 = 1 := h
    have h2 : (5 * n^3 + 6 * n^5 + 4 * a * n) % 3 = 0 := by
      have ha1 : a % 3 = 1 := by 
        omega
      have h6 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
        omega
      have h7 : (5 * n ^ 3 + 6 * n ^ 5 + 4 * a * n) % 3 = 0 := by
        rcases h6 with (h | h | h) <;> 
          simp [Int.add_emod, Int.mul_emod, pow_succ, h, ha1]
        <;> omega 
      assumption 
    have h3' : (5 * n^3 + 6 * n^5 + 4 * a * n) % 5 = 0 := by 
      have ha2 : a % 5 = 1 := by 
        omega 
      have h6 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
        omega
      have h7 : (5 * n^3 + 6 * n^5 + 4 * a * n) % 5 = 0 := by
        rcases h6 with (h | h | h | h | h) <;> 
          simp [Int.add_emod, Int.mul_emod, pow_succ, h, show a % 5 = 1 by omega]
        <;> omega 
      assumption 
    omega