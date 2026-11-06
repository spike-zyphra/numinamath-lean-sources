import Mathlib

theorem number_theory_215653 (N : ℕ) :
    (Nat.digits 10 (N * (N - 1))).sum ≠ (Nat.digits 10 ((N + 1)^2)).sum := by 
  by_contra h
  have h3 : N * (N - 1) % 9 = (Nat.digits 10 (N * (N - 1))).sum % 9 := by
    rw [Nat.modEq_nine_digits_sum (N * (N - 1))]
  have h4 : (N + 1) ^ 2 % 9 = (Nat.digits 10 ((N + 1) ^ 2)).sum % 9 := by
    rw [Nat.modEq_nine_digits_sum ((N + 1) ^ 2)]
  have h5 : (N * (N - 1)) % 9 = (N + 1) ^ 2 % 9 := by
    have h6 : (Nat.digits 10 (N * (N - 1))).sum % 9 = (Nat.digits 10 ((N + 1) ^ 2)).sum % 9 := by
      omega
    omega
  have h7 : (N + 1) ^ 2 = N * (N - 1) + 3 * N + 1 := by
    cases N with
    | zero => 
      omega
    | succ N => 
      cases N with 
      | zero => 
        omega
      | succ N => 
        simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul]
        <;> ring_nf <;> omega
  have h10 : (N * (N - 1) + 3 * N + 1) % 9 = 0 := by
    omega
  have h9 : N % 9 = 0 ∨ N % 9 = 1 ∨ N % 9 = 2 ∨ N % 9 = 3 ∨ N % 9 = 4 ∨ N % 9 = 5 ∨ N % 9 = 6 ∨ N % 9 = 7 ∨ N % 9 = 8 := by
    omega
  rcases h9 with (h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9) <;> simp [pow_two, Nat.mul_mod, h9, Nat.add_mod, Nat.mul_mod, Nat.sub_mod_eq_zero_of_mod_eq] at h10 h5 <;> omega