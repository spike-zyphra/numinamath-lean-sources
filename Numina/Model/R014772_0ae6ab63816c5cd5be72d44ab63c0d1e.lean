import Mathlib

theorem number_theory_255165 (x p : ℕ) (hp : Nat.Prime p) (h : x^3 - x + p = 507) :
    x = 8 := by
  have h1 : x ≤ 8 := by
    by_contra h2
    push_neg at h2
    have h2' : x ≥ 9 := by omega
    have h3 : x^3 - x > 507 := by
      have h4 : x ≥ 9 := h2'
      have h5 : x^3 ≥ 729 := by
        have h6 : x ≥ 9 := h4
        have h7 : x^3 ≥ 9^3 := by
          apply Nat.pow_le_pow_left
          all_goals linarith
        norm_num at h7 ⊢
        omega
      have h6 : x - 1 ≥ 8 := by omega
      have h7 : x + 1 ≥ 10 := by omega
      have h8 : x^3 - x ≥ 720 := by
        have h9 : x^3 - x = x * (x - 1) * (x + 1) := by
          cases x with
          | zero => linarith -- contradicts h2'
          | succ x =>
            cases x with
            | zero => nlinarith -- contradicts h2'
            | succ x =>
              simp [Nat.mul_assoc, Nat.succ_eq_add_one, Nat.add_assoc, Nat.mul_comm]
              <;> ring_nf <;> omega
        rw [h9]
        have h10 : x * (x - 1) * (x + 1) ≥ 9 * 8 * 10 := by
          have h11 : x ≥ 9 := h2'
          have h12 : x - 1 ≥ 8 := by omega
          have h13 : x + 1 ≥ 10 := by omega
          have h14 : x * (x - 1) ≥ 9 * 8 := by
            nlinarith [show x ≥ 9 by omega, show x - 1 ≥ 8 by omega]
          have h15 : (x * (x - 1)) * (x + 1) ≥ (9 * 8) * 10 := by
            nlinarith [show x * (x - 1) ≥ 9 * 8 by omega, show x + 1 ≥ 10 by omega]
          linarith
        omega
      omega
    omega
  interval_cases x <;> try { 
    omega
  }
  <;> try { 
    have : p ≤ 507 := by 
      omega
    interval_cases p <;> norm_num at hp h ⊢ 
    <;> all_goals omega 
  }