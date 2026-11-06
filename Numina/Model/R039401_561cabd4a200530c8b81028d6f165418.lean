import Mathlib

theorem number_theory_60627 (m n : ℕ) (hm : m^3 = 61629875) (hn : n^7 = 170859375) :
    100 * m + n = 39515 := by
  have h1 : m = 395 := by
    have h2 : m^3 = 61629875 := hm
    have h3 : m ≤ 395 := by
      by_contra h
      push_neg at h
      have h4 : m ^ 3 > 61629875 := by
        have h5 : m ≥ 396 := by linarith
        have h6 : m ^ 3 ≥ 396 ^ 3 := by
          apply Nat.pow_le_pow_of_le_left
          linarith
        have h7 : 396 ^ 3 > 61629875 := by norm_num
        linarith
      linarith
    have h4 : m ≥ 395 := by
      by_contra h
      push_neg at h
      have h5 : m ^ 3 < 61629875 := by
        have h6 : m ≤ 394 := by linarith
        have h7 : m ^ 3 ≤ 394 ^ 3 := by
          apply Nat.pow_le_pow_of_le_left
          linarith
        have h8 : 394 ^ 3 < 61629875 := by norm_num
        linarith
      linarith
    linarith
  have h2 : n = 15 := by
    have h3 : n^7 = 170859375 := hn
    have h4 : n ≤ 15 := by
      by_contra h
      push_neg at h
      have h5 : n ^ 7 > 170859375 := by
        have h6 : n ≥ 16 := by linarith
        have h7 : n ^ 7 ≥ 16 ^ 7 := by
          apply Nat.pow_le_pow_of_le_left
          linarith
        have h8 : 16 ^ 7 > 170859375 := by norm_num
        linarith
      linarith
    have h8 : n ≥ 15 := by
      by_contra h
      push_neg at h
      have h5 : n ^ 7 < 170859375 := by
        have h6 : n ≤ 14 := by linarith
        have h7 : n ^ 7 ≤ 14 ^ 7 := by
          apply Nat.pow_le_pow_of_le_left
          linarith
        have h8 : 14 ^ 7 < 170859375 := by norm_num
        linarith
      linarith
    linarith
  calc
    100 * m + n = 100 * 395 + 15 := by rw [h1, h2]
    _ = 39515 := by norm_num