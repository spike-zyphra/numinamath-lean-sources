import Mathlib

theorem number_theory_282524 (x y z : ℕ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h : 2^x + 2^y + 2^z = 2336) : x + y + z = 24 := by

  have h1 : x ≤ 11 := by
    by_contra h1
    push_neg at h1
    have h2 : 2^x ≥ 2^12 := by
      have h3 : x ≥ 12 := by omega
      have h4 : 2^x ≥ 2^12 := by
        apply Nat.pow_le_pow_of_le_right
        all_goals omega
      linarith
    have h2' : 2^y ≥ 2 := by
      have h3 : y ≥ 1 := by linarith
      have h4 : 2^y ≥ 2 := by
        have h5 : 2^y ≥ 2^1 := by
          apply Nat.pow_le_pow_of_le_right
          all_goals omega
        have h6 : 2^1 = 2 := by norm_num
        linarith [h5, h6]
      linarith
    have h2'' : 2^z ≥ 2 := by
      have h3 : z ≥ 1 := by linarith
      have h4 : 2^z ≥ 2 := by
        have h5 : 2^z ≥ 2^1 := by
          apply Nat.pow_le_pow_of_le_right
          all_goals omega
        have h6 : 2^1 = 2 := by norm_num
        linarith [h5, h6]
      linarith
    linarith
  have h2 : y ≤ 11 := by
    by_contra h1
    push_neg at h1
    have h2 : 2^y ≥ 2^12 := by
      have h3 : y ≥ 12 := by omega
      have h4 : 2^y ≥ 2^12 := by
        apply Nat.pow_le_pow_of_le_right
        all_goals omega
      linarith
    have h2' : 2^x ≥ 2 := by
      have h3 : x ≥ 1 := by linarith
      have h4 : 2^x ≥ 2 := by
        have h5 : 2^x ≥ 2^1 := by
          apply Nat.pow_le_pow_of_le_right
          all_goals omega
        have h6 : 2^1 = 2 := by norm_num
        linarith [h5, h6]
      linarith
    have h2'' : 2^z ≥ 2 := by
      have h3 : z ≥ 1 := by linarith
      have h4 : 2^z ≥ 2 := by
        have h5 : 2^z ≥ 2^1 := by
          apply Nat.pow_le_pow_of_le_right
          all_goals omega
        have h6 : 2^1 = 2 := by norm_num
        linarith [h5, h6]
      linarith
    linarith
  have h3 : z ≤ 11 := by
    by_contra h1
    push_neg at h1
    have h2 : 2^z ≥ 2^12 := by
      have h3 : z ≥ 12 := by omega
      have h4 : 2^z ≥ 2^12 := by
        apply Nat.pow_le_pow_of_le_right
        all_goals omega
      linarith
    have h2' : 2^x ≥ 2 := by
      have h3 : x ≥ 1 := by linarith
      have h4 : 2^x ≥ 2 := by
        have h5 : 2^x ≥ 2^1 := by
          apply Nat.pow_le_pow_of_le_right
          all_goals omega
        have h6 : 2^1 = 2 := by norm_num
        linarith [h5, h6]
      linarith
    have h2'' : 2^y ≥ 2 := by
      have h3 : y ≥ 1 := by linarith
      have h4 : 2^y ≥ 2 := by
        have h5 : 2^y ≥ 2^1 := by
          apply Nat.pow_le_pow_of_le_right
          all_goals omega
        have h6 : 2^1 = 2 := by norm_num
        linarith [h5, h6]
      linarith
    linarith
  interval_cases x <;> interval_cases y <;> interval_cases z <;> omega