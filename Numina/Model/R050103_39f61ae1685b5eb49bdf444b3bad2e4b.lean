import Mathlib

theorem algebra_153477 (x : ℕ) :
    2^x + 2^(x - 1) - 2^(x - 3) = 44 ↔ x = 5 := by 
  constructor
  · -- Assume 2^x + 2^(x - 1) - 2^(x - 3) = 44, prove x = 5
    intro h
    have h1 : x ≥ 3 := by
      by_contra h2
      push_neg at h2
      -- x < 3
      interval_cases x <;> norm_num at h ⊢ <;> try { all_goals contradiction }
    have h2 : 2 ^ x + 2 ^ (x - 1) - 2 ^ (x - 3) = 44 := h
    have eq1 : 2 ^ x + 2 ^ (x - 1) - 2 ^ (x - 3) = 2 ^ (x - 3) * 11 := by
      cases x with
      | zero =>
        exfalso
        all_goals omega
      | succ x =>
        cases x with
        | zero =>
          exfalso
          all_goals omega
        | succ x =>
          cases x with
          | zero =>
            exfalso
            all_goals omega
          | succ x =>
            simp [pow_succ, mul_add, add_assoc] at *
            <;> ring_nf
            <;> omega
    have h3 : 2 ^ (x - 3) * 11 = 44 := by 
      omega
    have h4 : 2 ^ (x - 3) = 4 := by
      omega
    have h5 : x - 3 = 2 := by 
      have h6 : 2 ^ (x - 3) = 4 := h4
      have h7 : x - 3 = 2 := by 
        exact Nat.pow_right_injective (by norm_num) h6
      exact h7
    omega
  · -- Assume x = 5, prove 2^x + 2^(x - 1) - 2^(x - 3) = 44
    intro h
    rw [h]
    norm_num