import Mathlib

theorem number_theory_22874 :
    IsLeast {x | ∃ n a b, n > 3 ∧ a > 3 ∧ b > 3 ∧ x = a + b ∧
      Nat.digits a n = [2, 3] ∧ Nat.digits b n = [3, 2]} 12 := by
  constructor
  · -- Show 12 is in the set
    use 17, 5, 7
    all_goals norm_num
  · -- Show there is no smaller element in the set
    intro x hx
    rcases hx with ⟨n, a, b, hn, ha, hb, h1, h2, h3⟩
    by_contra h
    push_neg at h
    -- Assume x < 12
    have h8 : x < 12 := h
    rw [h1] at h8
    have h3a : a + b < 12 := h8
    have h4 : n = 3 * a + 2 := by
      rw [← Nat.ofDigits_digits a n]
      rw [h2]
      simp [Nat.ofDigits, mul_add, mul_one]
      all_goals omega
    have h5 : n = 2 * b + 3 := by
      rw [← Nat.ofDigits_digits b n]
      rw [h3]
      simp [Nat.ofDigits, mul_add, mul_one]
      all_goals omega
    have h6 : 3 * a + 2 = 2 * b + 3 := by
      linarith [h4, h5]
    have h7 : 3 * a - 2 * b = 1 := by
      omega
    have h8 : a ≤ 8 := by
      omega
    have h9 : b ≤ 8 := by
      omega
    interval_cases a <;> interval_cases b <;> omega