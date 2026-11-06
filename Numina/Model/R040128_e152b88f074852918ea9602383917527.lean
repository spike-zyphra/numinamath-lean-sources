import Mathlib

theorem number_theory_263018 (a b c : ℕ) (h : 2^a * 3^b * 5^c = 36000) :
    3 * a + 4 * b + 6 * c = 41 := by

  have h1 : a ≤ 15 := by
    by_contra h1
    push_neg at h1
    have h2 : 2^a * 3^b * 5^c ≥ 2^16 * 3^0 * 5^0 := by
      have h3 : a ≥ 16 := by omega
      have h4 : b ≥ 0 := by omega
      have h5 : c ≥ 0 := by omega
      have h6 : 2^a ≥ 2^16 := by
        exact Nat.pow_le_pow_of_le_right (by norm_num) h3
      have h7 : 3^b ≥ 3^0 := by
        exact Nat.pow_le_pow_of_le_right (by norm_num) h4
      have h8 : 5^c ≥ 5^0 := by
        exact Nat.pow_le_pow_of_le_right (by norm_num) h5
      have h9 : 2^a * 3^b ≥ 2^16 * 3^0 := by
        nlinarith [h6, h7]
      have h10 : 2^a * 3^b * 5^c ≥ 2^16 * 3^0 * 5^0 := by
        nlinarith [h9, h8]
      linarith
    norm_num at h2 h
    all_goals omega

  have h2 : b ≤ 10 := by
    by_contra h2
    push_neg at h2
    have h3 : 2^a * 3^b * 5^c ≥ 2^0 * 3^11 * 5^0 := by
      have h4 : a ≥ 0 := by omega
      have h5 : b ≥ 11 := by omega
      have h6 : c ≥ 0 := by omega
      have h7 : 2^a ≥ 2^0 := by
        exact Nat.pow_le_pow_of_le_right (by norm_num) h4
      have h8 : 3^b ≥ 3^11 := by
        exact Nat.pow_le_pow_of_le_right (by norm_num) h5
      have h9 : 5^c ≥ 5^0 := by
        exact Nat.pow_le_pow_of_le_right (by norm_num) h6
      have h10 : 2^a * 3^b ≥ 2^0 * 3^11 := by
        nlinarith [h7, h8]
      have h11 : 2^a * 3^b * 5^c ≥ 2^0 * 3^11 * 5^0 := by
        nlinarith [h10, h9]
      linarith
    norm_num at h3 h
    all_goals omega

  have h3 : c ≤ 7 := by
    by_contra h3
    push_neg at h3
    have h4 : 2^a * 3^b * 5^c ≥ 2^0 * 3^0 * 5^8 := by
      have h5 : a ≥ 0 := by omega
      have h6 : b ≥ 0 := by omega
      have h7 : c ≥ 8 := by omega
      have h8 : 2^a ≥ 2^0 := by
        exact Nat.pow_le_pow_of_le_right (by norm_num) h5
      have h9 : 3^b ≥ 3^0 := by
        exact Nat.pow_le_pow_of_le_right (by norm_num) h6
      have h10 : 5^c ≥ 5^8 := by
        exact Nat.pow_le_pow_of_le_right (by norm_num) h7
      have h11 : 2^a * 3^b ≥ 2^0 * 3^0 := by
        nlinarith [h8, h9]
      have h12 : 2^a * 3^b * 5^c ≥ 2^0 * 3^0 * 5^8 := by
        nlinarith [h11, h10]
      linarith
    norm_num at h4 h
    all_goals omega

  interval_cases c <;> interval_cases a <;> interval_cases b <;> norm_num at h ⊢ <;> omega