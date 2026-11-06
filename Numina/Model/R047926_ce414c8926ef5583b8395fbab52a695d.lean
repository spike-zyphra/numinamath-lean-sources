import Mathlib

theorem number_theory_113344 (A : ℕ) (hA : A > 0) (h31 : ∃ r c, r < 100 ∧ c < A ∧ (r * A + c + 1) = 31) :
    ∃ r c, r < 100 ∧ c < A ∧ (r * A + c + 1) = 100 := by 
  use 99 / A, 99 % A
  constructor
  · 
    have h21 : A > 0 := hA
    have h80 : 99 / A ≤ 99 := by
      have h35 : A ≥ 1 := by omega
      have h52 : 99 / A ≤ 99 := by
        apply Nat.div_le_of_le_mul
        all_goals
          omega
      linarith
    omega
  constructor
  · 
    have h22 : 99 % A < A := by 
      have h21 : A > 0 := hA
      apply Nat.mod_lt 
      linarith
    linarith
  · 
    have h87 : (99 / A) * A + 99 % A + 1 = 100 := by
      have h82 : (99 / A) * A + 99 % A = 99 := by
        have h84 : A > 0 := hA
        have h115 : A * (99 / A) + 99 % A = 99 := Nat.div_add_mod 99 A
        have h116 : (99 / A) * A + 99 % A = A * (99 / A) + 99 % A := by 
          ring
        rw [h116] 
        exact h115
      omega
    linarith