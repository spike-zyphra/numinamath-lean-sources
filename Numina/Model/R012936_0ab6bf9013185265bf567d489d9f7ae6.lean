import Mathlib

theorem algebra_288419 {b : ℕ} (hb : b > 1) (h : Nat.digits b (33 * 62) = [2, 3, 1, 5]) :
    Nat.digits b (12 + 15 + 16) = [4, 4] := by
  have h1 : b ≤ 12 := by
    by_contra h2
    push_neg at h2
    have h3 : b ≥ 13 := by omega
    have h4 : Nat.digits b (33 * 62) = [2, 3, 1, 5] := h
    have h5 : Nat.ofDigits b (Nat.digits b (33 * 62)) = 33 * 62 := by
      rw [Nat.ofDigits_digits]
    have h6 : Nat.ofDigits b (Nat.digits b (33 * 62)) = 5 * b ^ 3 + b ^ 2 + 3 * b + 2 := by
      rw [h4]
      simp [Nat.ofDigits]
      all_goals ring
    rw [h6] at h5
    have h9 : b ≥ 13 := h3
    have h10 : 5 * b ^ 3 + b ^ 2 + 3 * b + 2 ≥ 5 * 13 ^ 3 + 13 ^ 2 + 3 * 13 + 2 := by
      have h11 : b ≥ 13 := h9
      have h12 : (5 * b ^ 3 + b ^ 2 + 3 * b + 2 : ℕ) ≥ (5 * 13 ^ 3 + 13 ^ 2 + 3 * 13 + 2 : ℕ) := by
        have h13 : b ≥ 13 := h11
        have h14 : (b: ℕ) ≥ (13: ℕ) := h13
        have h15 : (b^2 : ℕ) ≥ (13^2 : ℕ) := by nlinarith [h14]
        have h16 : (b^3 : ℕ) ≥ (13^3 : ℕ) := by 
          have h17 : (b : ℕ) ≥ (13 : ℕ) := h14
          have h18 : b ^ 3 ≥ 13 ^ 3 := by apply Nat.pow_le_pow_of_le_left h17 3
          linarith
        nlinarith [show (b : ℕ) ≥ (13 : ℕ) from h14, show (b ^ 2 : ℕ) ≥ (13 ^ 2 : ℕ) from h15, 
          show (b ^ 3 : ℕ) ≥ (13 ^ 3 : ℕ) from h16]
      omega
    have h11 : 5 * 13 ^ 3 + 13 ^ 2 + 3 * 13 + 2 > 2046 := by norm_num
    have h12 : 5 * b ^ 3 + b ^ 2 + 3 * b + 2 > 2046 := by linarith [h10, h11]
    omega
  have h9 : b ≤ 12 := h1
  have h4 : Nat.digits b (33 * 62) = [2, 3, 1, 5] := h
  interval_cases b <;> norm_num at h4 ⊢
  <;> try { contradiction }