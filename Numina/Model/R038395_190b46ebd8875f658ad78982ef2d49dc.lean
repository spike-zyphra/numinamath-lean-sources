import Mathlib

theorem number_theory_43811 (n : ℕ) (h₀ : 100 ≤ n) (h₁ : n < 1000) :
    n = (Nat.digits 10 n).headI^3 + (Nat.digits 10 n).tail.headI^3 + (Nat.digits 10 n).tail.tail.headI^3 ↔
    n = 153 ∨ n = 370 ∨ n = 371 ∨ n = 407 := by
  constructor
  · -- First, prove the forward direction: if n equals the sum of the cubes of its digits, then it must be one of {153, 370, 371, 407}
    intro h
    interval_cases n <;> norm_num at h ⊢ <;> omega
  · -- Now, prove the backward direction: each of {153, 370, 371, 407} equals the sum of the cubes of its digits
    rintro (h | h | h | h)
    · -- Show that 153 satisfies the condition.
      rw [h]
      norm_num
    · -- Show that 370 satisfies the condition.
      rw [h]
      norm_num
    · -- Show that 371 satisfies the condition.
      rw [h]
      norm_num
    · -- Show that 407 satisfies the condition.
      rw [h]
      norm_num