import Mathlib

theorem number_theory_83694 : { (a, b, c, d) : ℕ × ℕ × ℕ × ℕ | 5^a + 6^b + 7^c + 11^d = 1999} = {(4, 2, 1, 3)} := by
  ext ⟨a, b, c, d⟩
  simp
  constructor
  · -- First, prove that (4, 2, 1, 3) is the only solution
    rintro H
    have h1 : a ≤ 4 := by
      by_contra h
      push_neg at h
      have h2 : 5 ^ a ≥ 5 ^ 5 := by
        apply Nat.pow_le_pow_of_le_right
        all_goals norm_num
        all_goals omega
      have h3 : 5 ^ 5 ≥ 3125 := by norm_num
      have h4 : 5 ^ a ≥ 3125 := by linarith [h2, h3]
      have h5 : 5 ^ a + 6 ^ b + 7 ^ c + 11 ^ d ≥ 5 ^ a := by
        linarith [show 6 ^ b ≥ 0 by positivity, show 7 ^ c ≥ 0 by positivity, show 11 ^ d ≥ 0 by positivity]
      linarith [h5, h4, H]
    have h2 : b ≤ 4 := by
      by_contra h
      push_neg at h
      have h3 : 6 ^ b ≥ 6 ^ 5 := by
        apply Nat.pow_le_pow_of_le_right
        all_goals norm_num
        all_goals omega
      have h4 : 6 ^ 5 ≥ 7776 := by norm_num
      have h5 : 6 ^ b ≥ 7776 := by linarith [h3, h4]
      have h6 : 5 ^ a + 6 ^ b + 7 ^ c + 11 ^ d ≥ 6 ^ b := by
        linarith [show 5 ^ a ≥ 0 by positivity, show 7 ^ c ≥ 0 by positivity, show 11 ^ d ≥ 0 by positivity]
      linarith [h6, h5, H]
    have h3 : c ≤ 3 := by
      by_contra h
      push_neg at h
      have h4 : 7 ^ c ≥ 7 ^ 4 := by
        apply Nat.pow_le_pow_of_le_right
        all_goals norm_num
        all_goals omega
      have h5 : 7 ^ 4 ≥ 2401 := by norm_num
      have h6 : 7 ^ c ≥ 2401 := by linarith [h4, h5]
      have h7 : 5 ^ a + 6 ^ b + 7 ^ c + 11 ^ d ≥ 7 ^ c := by
        linarith [show 5 ^ a ≥ 0 by positivity, show 6 ^ b ≥ 0 by positivity, show 11 ^ d ≥ 0 by positivity]
      linarith [h7, h6, H]
    have h4 : d ≤ 3 := by
      by_contra h
      push_neg at h
      have h5 : 11 ^ d ≥ 11 ^ 4 := by
        apply Nat.pow_le_pow_of_le_right
        all_goals norm_num
        all_goals omega
      have h6 : 11 ^ 4 ≥ 14641 := by norm_num
      have h7 : 11 ^ d ≥ 14641 := by linarith [h5, h6]
      have h8 : 5 ^ a + 6 ^ b + 7 ^ c + 11 ^ d ≥ 11 ^ d := by
        linarith [show 5 ^ a ≥ 0 by positivity, show 6 ^ b ≥ 0 by positivity, show 7 ^ c ≥ 0 by positivity]
      linarith [h8, h7, H]
    interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d
    <;> norm_num at H
    <;> tauto
  · -- Show that (4, 2, 1, 3) is a solution
    rintro ⟨rfl, rfl, rfl, rfl⟩
    all_goals norm_num