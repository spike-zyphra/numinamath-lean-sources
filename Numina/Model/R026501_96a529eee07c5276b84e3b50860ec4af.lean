import Mathlib

theorem number_theory_327688 (a b c : ℕ) (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c)
    (h : a * b^2 * c^3 = 675) : a + b + c ≤ 79 := by 
  by_contra h19
  push_neg at h19
  have h10 : a * b ^ 2 * c ^ 3 = 675 := h
  have h10' : c ≤ 8 := by 
    by_contra h11
    push_neg at h11
    have h12 : c ^ 3 ≥ 729 := by
      have h13 : c ≥ 9 := by omega
      have h14 : c ^ 3 ≥ 9 ^ 3 := by
        apply Nat.pow_le_pow_left
        all_goals linarith
      norm_num at h14 ⊢
      all_goals nlinarith
    have h13 : a * b ^ 2 ≥ 1 := by
      have h16 : a ≥ 1 := by
        by_contra h17
        push_neg at h17
        have h18 : a = 0 := by linarith
        rw [h18] at h
        nlinarith
      have h17 : b ^ 2 ≥ 1 := by
        have hb1 : b ≥ 1 := by
          by_contra h17
          push_neg at h17
          have h17 : b = 0 := by linarith
          rw [h17] at h
          nlinarith
        have h16 : b ^ 2 ≥ 1 := by
          nlinarith
        nlinarith
      nlinarith
    nlinarith
    <;> nlinarith
  interval_cases c <;> try { 
    norm_num at h10
    all_goals
    have h11 : b ≤ 31 := by
      by_contra h12
      push_neg at h12
      have h20 : a = 0 := by
        nlinarith
      simp [h20] at h10
      all_goals
      omega
    interval_cases b <;> omega 
  }
  <;> norm_num at h10
  <;> try { 
    have h11 : b ≤ 31 := by
      by_contra h12
      push_neg at h12
      nlinarith
    interval_cases b <;> omega 
  }
  all_goals
  omega