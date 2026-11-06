import Mathlib
open Finset Set Nat  
set_option linter.unusedVariables false

/-2. Nanda and Mike both have a note with the same five-digit number on it. Nanda puts the digit 4 in front of her number and the digit 8 at the end, resulting in a seven-digit number. Mike puts a digit in front of his number. When they compare their new numbers, it turns out that Nanda's number is exactly 6 times larger than Mike's.
What number did they start with?-/
theorem number_theory_174971 (x c : ℕ) (hx : 10000 ≤ x ∧ x ≤ 99999)
  (hc : 1 ≤ c ∧ c ≤ 9) (h_eq : 4000008 + 10 * x = 6 * (100000 * c + x)) :
    x = 49998 := by
  -- Simplify the equation.
  have h_simplify : x = 150000 * c - 1000002 := by
    have h_eq_simp : 4 * x = 600000 * c - 4000008 := by omega
    have h_div_4 : 4 ∣ 600000 * c - 4000008 := by omega
    have h_x : x = (600000 * c - 4000008) / 4 := by
      rw [mul_comm] at h_eq_simp
      exact (Nat.div_eq_of_eq_mul_left (by norm_num : 0 < 4) h_eq_simp.symm).symm
    norm_num at h_x
    omega
  -- Check $c ≤ 6$ implies $x > 99999$.
  have h_c_le_6 : c ≤ 6 → x > 99999 := by
    intro h_c_le_6
    have h_x_bound : x = 150000 * c - 1000002 := h_simplify
    have h_x_le : x ≤ 150000 * 6 - 1000002 := by
      rw [h_x_bound]
      exact Nat.sub_le_sub_right (Nat.mul_le_mul_left 150000 h_c_le_6) 1000002
    norm_num at h_x_le
    linarith
  -- Check $c ≥ 8$ implies $x > 99999$.
  have h_c_ge_8 : c ≥ 8 → x > 99999 := by
    intro h_c_ge_8
    have h_x_bound : x = 150000 * c - 1000002 := h_simplify
    have h_x_ge : x ≥ 150000 * 8 - 1000002 := by
      rw [h_x_bound]
      exact Nat.sub_le_sub_right (Nat.mul_le_mul_left 150000 h_c_ge_8) 1000002
    norm_num at h_x_ge
    linarith
  -- Conclude $c = 7$.
  have h_c_eq_7 : c = 7 := by
    have h_c_not_le_6 : ¬c ≤ 6 := by
      intro h
      have h_x_large : x > 99999 := h_c_le_6 h
      linarith [hx.2]
    have h_c_not_ge_8 : ¬c ≥ 8 := by
      intro h
      have h_x_large : x > 99999 := h_c_ge_8 h
      linarith [hx.2]
    linarith [hc.1, hc.2]
  -- Compute $x = 49998$.
  have h_x_eq : x = 49998 := by
    rw [h_simplify, h_c_eq_7]
  exact h_x_eq
