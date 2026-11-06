import Mathlib

theorem number_theory_34744 (a b c d : ℤ) (h : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) :
    12 ∣ (a - b) * (a - c) * (a - d) * (b - c) * (b - d) * (c - d) := by 
  have h1 : a ≠ b := h.1
  have h2 : a ≠ c := h.2.1
  have h3 : a ≠ d := h.2.2.1
  have h4 : b ≠ c := h.2.2.2.1
  have h5 : b ≠ d := h.2.2.2.2.1
  have h6 : c ≠ d := h.2.2.2.2.2
  have h7 : (a - b) * (a - c) * (a - d) * (b - c) * (b - d) * (c - d) % 4 = 0 := by
    have h41 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
    have h42 : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by omega
    have h43 : c % 4 = 0 ∨ c % 4 = 1 ∨ c % 4 = 2 ∨ c % 4 = 3 := by omega
    have h44 : d % 4 = 0 ∨ d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by omega
    rcases h41 with (h41 | h41 | h41 | h41) <;> rcases h42 with (h42 | h42 | h42 | h42) <;> rcases h43 with (h43 | h43 | h43 | h43) <;> rcases h44 with (h44 | h44 | h44 | h44)
      <;> simp [Int.mul_emod, Int.add_emod, Int.sub_emod, h41, h42, h43, h44, Int.mul_emod, Int.add_emod, Int.sub_emod]
      <;> omega
  have h8 : (a - b) * (a - c) * (a - d) * (b - c) * (b - d) * (c - d) % 3 = 0 := by
    have h31 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
    have h32 : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
    have h33 : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2 := by omega
    have h34 : d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 := by omega
    rcases h31 with (h31 | h31 | h31) <;> rcases h32 with (h32 | h32 | h32) <;> rcases h33 with (h33 | h33 | h33) <;> rcases h34 with (h34 | h34 | h34)
      <;> simp [Int.mul_emod, Int.add_emod, Int.sub_emod, h31, h32, h33, h34, Int.mul_emod, Int.add_emod, Int.sub_emod]
      <;> omega
  omega