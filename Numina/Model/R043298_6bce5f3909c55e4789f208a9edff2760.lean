import Mathlib

theorem number_theory_64488 :
    IsLeast {x : ℤ | ∃ p q r : ℤ, p ≠ 0 ∧ q ≠ 0 ∧ r ≠ 0 ∧ p^2 + q^2 = r^2 ∧ (p + q + r)^2 = x} 4 := by
  constructor
  · -- First part: show 4 is in the set
    use 4, 3, -5
    all_goals
      norm_num
  · -- Second part: show 4 is minimal
    intro x hx
    rcases hx with ⟨p, q, r, hp, hq, hr, heq1, heq2⟩
    by_contra h
    push_neg at h
    have h1 : (p + q + r) ^ 2 < (4 : ℤ) := by
      nlinarith
    have h2 : (p + q + r) ^ 2 ≥ 0 := by
      apply sq_nonneg
    have h3 : (p + q + r) ^ 2 = 0 ∨ (p + q + r) ^ 2 = 1 ∨ (p + q + r) ^ 2 = 2 ∨ (p + q + r) ^ 2 = 3 := by
      have h4 : (p + q + r) ^ 2 < (4 : ℤ) := h1
      have h5 : (p + q + r) ^ 2 ≥ 0 := h2
      omega
    rcases h3 with (h3 | h3 | h3 | h3)
    · -- Case (p + q + r) ^ 2 = 0
      have h7 : (p + q + r) = 0 := by
        nlinarith
      have h8 : r = -p - q := by linarith
      rw [h8] at heq1
      have h9 : p * q = 0 := by
        nlinarith
      cases (mul_eq_zero.1 h9) with
      | inl h10 =>
        exfalso
        exact hp (by linarith)
      | inr h11 =>
        exfalso
        exact hq (by linarith)
    · -- Case (p + q + r) ^ 2 = 1
      have h7 : (p + q + r) = 1 ∨ (p + q + r) = -1 := by
        have h10 : (p + q + r) ^ 2 = 1 := by
          linarith
        have h11 : (p + q + r) = 1 ∨ (p + q + r) = -1 := by
          rw [sq_eq_one_iff] at h10
          tauto
        assumption
      rcases h7 with (h7 | h7)
      · -- Case p + q + r = 1
        have h8 : p + q = 1 - r := by
          linarith
        have h9 : 2 * (p * q) = 1 - 2 * r := by
          have h10 : p ^ 2 + q ^ 2 = r ^ 2 := heq1
          have h11 : (p + q) ^ 2 = (1 - r) ^ 2 := by
            rw [h8]
          have h12 : (p + q) ^ 2 = p ^ 2 + 2 * (p * q) + q ^ 2 := by ring
          rw [h12] at h11
          nlinarith
        omega
      · -- Case p + q + r = -1
        have h8 : p + q = -1 - r := by
          linarith
        have h9 : 2 * (p * q) = 1 + 2 * r := by
          have h10 : p ^ 2 + q ^ 2 = r ^ 2 := heq1
          have h11 : (p + q) ^ 2 = (-1 - r) ^ 2 := by
            rw [h8]
          have h12 : (p + q) ^ 2 = p ^ 2 + 2 * (p * q) + q ^ 2 := by ring
          rw [h12] at h11
          nlinarith
        omega
    · -- Case (p + q + r) ^ 2 = 2
      have h11 : (p + q + r)^2 = 2 := by
        linarith
      have h10 : (p + q + r)^2 % 4 = 0 ∨ (p + q + r)^2 % 4 = 1 := by
        have h11 : (p + q + r) % 4 = 0 ∨ (p + q + r) % 4 = 1 ∨ (p + q + r) % 4 = 2 ∨ (p + q + r) % 4 = 3 := by 
          omega
        rcases h11 with (h | h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
      omega
    · -- Case (p + q + r) ^ 2 = 3
      have h11 : (p + q + r)^2 = 3 := by
        linarith
      have h10 : (p + q + r)^2 % 4 = 0 ∨ (p + q + r)^2 % 4 = 1 := by
        have h11 : (p + q + r) % 4 = 0 ∨ (p + q + r) % 4 = 1 ∨ (p + q + r) % 4 = 2 ∨ (p + q + r) % 4 = 3 := by 
          omega
        rcases h11 with (h | h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
      omega