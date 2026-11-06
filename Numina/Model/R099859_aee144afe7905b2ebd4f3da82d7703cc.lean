import Mathlib

theorem algebra_221692 (n : ℕ) (hn : n > 0) (h : 1 / n = 24 / (n - 1) + 5) :
    1 / n = 40 := by
  have h1 : n ≥ 1 := by linarith
  by_cases h2 : n > 1
  · -- If n > 1, then n ≥ 2
    have h3 : n ≥ 2 := by linarith
    have h4 : 1 / n = 0 := by
      norm_num
      omega
    have h5 : 24 / (n - 1) + 5 = 0 := by linarith [h, h4]
    have h6 : 24 / (n - 1) > 0 := by
      have h8 : n - 1 > 0 := by
        omega
      have h7 : 24 / (n - 1) > 0 := by
        apply Nat.pos_of_ne_zero
        by_contra h8
        have h9 : 24 / (n - 1) = 0 := by omega
        have h10 : n - 1 > 24 := by
          have : 24 / (n - 1) = 0 := h9
          have : n - 1 > 24 := by
            by_contra h'
            push_neg at h'
            interval_cases (n - 1) <;> omega
          linarith
        have h11 : n > 25 := by omega
        have h12 : n - 1 > 24 := by omega
        omega
      linarith
    omega
  · -- If n ≤ 1, so n = 1
    have h7 : n = 1 := by linarith
    rw [h7] at h
    norm_num at h
    all_goals omega