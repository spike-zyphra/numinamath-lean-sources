import Mathlib

theorem number_theory_97281 (w x y z : ℕ) (h : 2^w * 3^x * 5^y * 7^z = 588) : 2 * w + 3 * x + 5 * y + 7 * z = 21 := by
  have h1 : w ≤ 10 := by
    by_contra H
    push_neg at H
    have h2 : 2^w * 3^x * 5^y * 7^z = 588 := h
    have h3 : 2^w ≥ 2^11 := by
      have h4 : w ≥ 11 := by linarith
      have h5 : 2^w ≥ 2^11 := by
        exact (Nat.pow_le_pow_of_le_right (by norm_num) h4)
      linarith
    have h4 : 2^w * 3^x * 5^y * 7^z > 588 := by
      have h5 : 3^x ≥ 1 := by
        apply Nat.one_le_pow
        norm_num
        all_goals omega
      have h6 : 5^y ≥ 1 := by
        apply Nat.one_le_pow
        norm_num
        all_goals omega
      have h7 : 7^z ≥ 1 := by
        apply Nat.one_le_pow
        norm_num
        all_goals omega
      have h8 : 2^w * 3^x * 5^y * 7^z ≥ 2^w * 1 * 1 * 1 := by
        gcongr
        all_goals linarith
      have h9 : 2^w * 1 * 1 * 1 ≥ 2^11 := by
        linarith
      have h10 : 2^w * 3^x * 5^y * 7^z ≥ 2^11 := by
        linarith
      have h11 : 2^11 > 588 := by norm_num
      linarith
      all_goals linarith
    linarith
  have h2 : x ≤ 6 := by
    by_contra H
    push_neg at H
    have h3 : 2^w * 3^x * 5^y * 7^z = 588 := h
    have h4 : 3^x ≥ 3^7 := by
      have h5 : x ≥ 7 := by linarith
      have h6 : 3^x ≥ 3^7 := by
        exact (Nat.pow_le_pow_of_le_right (by norm_num) h5)
      linarith
    have h5 : 2^w * 3^x * 5^y * 7^z > 588 := by
      have h6 : 2^w ≥ 1 := by
        apply Nat.one_le_pow
        norm_num
        all_goals omega
      have h7 : 5^y ≥ 1 := by
        apply Nat.one_le_pow
        norm_num
        all_goals omega
      have h8 : 7^z ≥ 1 := by
        apply Nat.one_le_pow
        norm_num
        all_goals omega
      have h9 : 2^w * 3^x * 5^y * 7^z ≥ 1 * 3^7 * 1 * 1 := by
        gcongr
        all_goals linarith
      have h10 : 1 * 3^7 * 1 * 1 ≥ 3^7 := by
        norm_num
      have h11 : 2^w * 3^x * 5^y * 7^z ≥ 3^7 := by
        linarith
      have h12 : 3^7 > 588 := by norm_num
      linarith
      all_goals linarith
    linarith
  have h3 : y ≤ 3 := by
    by_contra H
    push_neg at H
    have h4 : 2^w * 3^x * 5^y * 7^z = 588 := h
    have h5 : 5^y ≥ 5^4 := by
      have h6 : y ≥ 4 := by linarith
      have h7 : 5^y ≥ 5^4 := by
        exact (Nat.pow_le_pow_of_le_right (by norm_num) h6)
      linarith
    have h6 : 2^w * 3^x * 5^y * 7^z > 588 := by
      have h7 : 2^w ≥ 1 := by
        apply Nat.one_le_pow
        norm_num
        all_goals omega
      have h8 : 3^x ≥ 1 := by
        apply Nat.one_le_pow
        norm_num
        all_goals omega
      have h9 : 7^z ≥ 1 := by
        apply Nat.one_le_pow
        norm_num
        all_goals omega
      have h10 : 2^w * 3^x * 5^y * 7^z ≥ 1 * 1 * 5^4 * 1 := by
        gcongr
        all_goals linarith
      have h11 : 1 * 1 * 5^4 * 1 ≥ 5^4 := by
        norm_num
      have h12 : 2^w * 3^x * 5^y * 7^z ≥ 5^4 := by
        linarith
      have h13 : 5^4 > 588 := by norm_num
      linarith
      all_goals linarith
    linarith
  have h4 : z ≤ 3 := by
    by_contra H
    push_neg at H
    have h5 : 2^w * 3^x * 5^y * 7^z = 588 := h
    have h6 : 7^z ≥ 7^4 := by
      have h7 : z ≥ 4 := by linarith
      have h8 : 7^z ≥ 7^4 := by
        exact (Nat.pow_le_pow_of_le_right (by norm_num) h7)
      linarith
    have h7 : 2^w * 3^x * 5^y * 7^z > 588 := by
      have h8 : 2^w ≥ 1 := by
        apply Nat.one_le_pow
        norm_num
        all_goals omega
      have h9 : 3^x ≥ 1 := by
        apply Nat.one_le_pow
        norm_num
        all_goals omega
      have h10 : 5^y ≥ 1 := by
        apply Nat.one_le_pow
        norm_num
        all_goals omega
      have h11 : 2^w * 3^x * 5^y * 7^z ≥ 1 * 1 * 1 * 7^4 := by
        gcongr
        all_goals linarith
      have h12 : 1 * 1 * 1 * 7^4 ≥ 7^4 := by
        norm_num
      have h13 : 2^w * 3^x * 5^y * 7^z ≥ 7^4 := by
        linarith
      have h14 : 7^4 > 588 := by norm_num
      linarith
      all_goals linarith
    linarith
  interval_cases w <;> interval_cases x <;> interval_cases y <;> interval_cases z
  <;> norm_num at h ⊢
  <;> omega