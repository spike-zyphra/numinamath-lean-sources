import Mathlib

theorem number_theory_188021 (b : ℕ) (hb : b ≥ 6) :
    (Nat.digits b ((b-1)^4))[0]? = some 1 ∧ (Nat.digits b ((b-1)^4))[2]? = some 5 := by
  have h1 : b ≥ 6 := hb
  have h3 : Nat.digits b ((b - 1) ^ 4) = [1, b - 4, 5, b - 4] := by
    have h4 : (b - 1 : ℕ) ^ 4 = 1 + (b - 4) * b + 5 * b ^ 2 + (b - 4) * b ^ 3 := by
      cases b with
      | zero => omega
      | succ b =>
        cases b with
        | zero => omega
        | succ b =>
          cases b with
          | zero => omega
          | succ b =>
            cases b with
            | zero => omega
            | succ b =>
              simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.pow_zero, Nat.mul_assoc, Nat.pow_succ, Nat.pow_zero]
              ring_nf
              <;> omega
    rw [h4]
    have h8 : Nat.ofDigits b [1, b - 4, 5, b - 4] = (1 + (b - 4) * b + 5 * b ^ 2 + (b - 4) * b ^ 3 : ℕ) := by
      simp [Nat.ofDigits, mul_add, add_mul, pow_succ, pow_zero, mul_assoc]
      all_goals
        ring_nf
        <;> omega
    have h9 : Nat.digits b ((1 + (b - 4) * b + 5 * b ^ 2 + (b - 4) * b ^ 3 : ℕ)) = [1, b - 4, 5, b - 4] := by
      rw [← h8]
      rw [Nat.digits_ofDigits]
      all_goals
        try { 
          simp at *
          all_goals
            omega
        }
    exact h9
  rw [h3]
  constructor
  · -- Show that [0]? = some 1
    simp
  · -- Show that [2]? = some 5
    simp