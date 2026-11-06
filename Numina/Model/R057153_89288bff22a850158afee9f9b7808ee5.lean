import Mathlib

theorem number_theory_273625 (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (h : 3 ^ x * 5 ^ y = 225) : x + y = 4 := by

  have h1 : x ≤ 4 := by
    by_contra h1
    push_neg at h1
    have h2 : x ≥ 5 := by omega
    have h3 : 3 ^ x ≥ 3 ^ 5 := by
      apply Nat.pow_le_pow_of_le_right (by norm_num) h2
    norm_num at h3 ⊢
    have h4 : 3 ^ x * 5 ^ y ≥ 3 ^ 5 * 5 ^ 0 := by
      have h5 : 3 ^ x ≥ 3 ^ 5 := h3
      have h6 : 5 ^ y ≥ 5 ^ 0 := by
        apply Nat.pow_le_pow_of_le_right (by norm_num) (by linarith [show y ≥ 0 by linarith [hy]])
      nlinarith only [h5, h6]
      all_goals linarith
    norm_num at h4 ⊢
    nlinarith only [h, h4]
    all_goals nlinarith only [h, h4]

  have h1' : y ≤ 3 := by
    by_contra h1'
    push_neg at h1'
    have h2' : y ≥ 4 := by omega
    have h3' : 5 ^ y ≥ 5 ^ 4 := by
      apply Nat.pow_le_pow_of_le_right (by norm_num) h2'
    norm_num at h3' ⊢
    have h4' : 3 ^ x * 5 ^ y ≥ 3 ^ 0 * 5 ^ 4 := by
      have h5' : 3 ^ x ≥ 3 ^ 0 := by
        apply Nat.pow_le_pow_of_le_right (by norm_num) (by linarith [show x ≥ 0 by linarith [hx]])
      have h6' : 5 ^ y ≥ 5 ^ 4 := h3'
      nlinarith only [h5', h6']
      all_goals linarith
    norm_num at h4' ⊢
    nlinarith only [h, h4']
    all_goals nlinarith only [h, h4']

  interval_cases x <;> interval_cases y <;> omega