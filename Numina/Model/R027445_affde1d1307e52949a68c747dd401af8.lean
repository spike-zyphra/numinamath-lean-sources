import Mathlib

theorem number_theory_284821 (x y z : ℕ) (h : 800670 = 8 * 10^x + 6 * 10^y + 7 * 10^z) :
    x + y + z = 8 := by
  have h1 : x ≤ 6 := by
    by_contra h1
    push_neg at h1
    have h2 : 8 * 10^x + 6 * 10^y + 7 * 10^z ≥ 8 * 10^7 := by
      have h3 : 8 * 10^x ≥ 8 * 10^7 := by
        have h4 : 10^x ≥ 10^7 := by
          have h5 : x ≥ 7 := by linarith
          have h6 : 10^x ≥ 10^7 := by
            apply Nat.pow_le_pow_of_le_right (by norm_num) h5
          linarith
        nlinarith
      have h4 : 6 * 10^y ≥ 0 := by positivity
      have h5 : 7 * 10^z ≥ 0 := by positivity
      linarith
    nlinarith
  have h2 : y ≤ 6 := by 
    by_contra h2
    push_neg at h2
    have h3 : 8 * 10^x + 6 * 10^y + 7 * 10^z ≥ 6 * 10^7 := by
      have h3 : 6 * 10^y ≥ 6 * 10^7 := by
        have h4 : 10^y ≥ 10^7 := by
          have h5 : y ≥ 7 := by linarith
          have h6 : 10^y ≥ 10^7 := by
            apply Nat.pow_le_pow_of_le_right (by norm_num) h5
          linarith
        nlinarith
      have h4 : 8 * 10^x ≥ 0 := by positivity
      have h5 : 7 * 10^z ≥ 0 := by positivity
      linarith
    nlinarith
  have h3 : z ≤ 6 := by
    by_contra h3
    push_neg at h3
    have h4 : 8 * 10^x + 6 * 10^y + 7 * 10^z ≥ 7 * 10^7 := by
      have h5 : 7 * 10^z ≥ 7 * 10^7 := by
        have h6 : 10^z ≥ 10^7 := by
          have h7 : z ≥ 7 := by linarith
          have h8 : 10^z ≥ 10^7 := by
            apply Nat.pow_le_pow_of_le_right (by norm_num) h7
          linarith
        nlinarith
      have h4 : 8 * 10^x ≥ 0 := by positivity
      have h5 : 6 * 10^y ≥ 0 := by positivity
      linarith
    nlinarith
  interval_cases x <;> interval_cases y <;> interval_cases z <;> omega