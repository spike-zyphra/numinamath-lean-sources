import Mathlib


lemma lemma_1 (n : ℕ) (h : 3 * n ^ 4 + 4 * n ^ 2 = 12544) : n = 8 := by
  have h1 : n ≤ 8 := by
    by_contra h2
    push_neg at h2
    have h2' : n ≥ 9 := by
      omega
    have h3 : 3 * n ^ 4 + 4 * n ^ 2 ≥ 20007 := by
      have h4 : n ≥ 9 := h2'
      have h5 : n ^ 2 ≥ 81 := by
        have h6 : n ≥ 9 := h4
        have h7 : n ^ 2 ≥ 9 ^ 2 := by
          apply Nat.pow_le_pow_of_le_left h6 2
        norm_num at h7 ⊢
        linarith
      have h8 : n ^ 4 ≥ 6561 := by
        have h9 : n ≥ 9 := h4
        have h10 : n ^ 4 ≥ 9 ^ 4 := by
          apply Nat.pow_le_pow_of_le_left h9 4
        norm_num at h10 ⊢
        linarith
      have h11 : 3 * n ^ 4 ≥ 19683 := by
        linarith [h8]
      have h12 : 4 * n ^ 2 ≥ 324 := by
        linarith [h5]
      linarith
    linarith
  have h2 : n ≥ 8 := by
    by_contra h3
    push_neg at h3
    have h3' : n ≤ 7 := by
      omega
    have h6 : 3 * n ^ 4 + 4 * n ^ 2 < 12544 := by
      interval_cases n <;> norm_num
    omega
  linarith


theorem number_theory_282638 (n : ℕ) (h : Nat.digits n 12551 = [7, 0, 4, 0, 3]) :
    n = 8 := by
  have h1 : 3 * n ^ 4 + 4 * n ^ 2 + 7 = 12551 := by
    have h2 : Nat.ofDigits n (Nat.digits n 12551) = 12551 := by
      rw [Nat.ofDigits_digits]
      all_goals linarith
    rw [h] at h2
    have eq1 : Nat.ofDigits n [7, 0, 4, 0, 3] = 3 * n ^ 4 + 4 * n ^ 2 + 7 := by
      simp [Nat.ofDigits, mul_add, add_mul, pow_two, pow_succ, pow_zero, mul_assoc]
      <;> ring_nf
    rw [eq1] at h2
    nlinarith
  have eq1 : 3 * n ^ 4 + 4 * n ^ 2 = 12544 := by
    nlinarith
  apply lemma_1 n eq1