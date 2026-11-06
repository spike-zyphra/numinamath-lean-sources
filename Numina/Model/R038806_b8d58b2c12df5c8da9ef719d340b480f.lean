import Mathlib

theorem number_theory_7336 (x y : ℕ) :
    2^x + 3 * 4^y = 2096 ↔ (x = 11 ∧ y = 2) := by
  constructor
  · -- Assume 2^x + 3 * 4^y = 2096, prove (x = 11 ∧ y = 2)
    intro h
    have h1 : x ≤ 11 := by
      by_contra h2
      push_neg at h2
      have h2' : 2^x ≥ 4096 := by
        have : x ≥ 12 := by linarith
        have h3 : 2^x ≥ 2^12 := by
          apply Nat.pow_le_pow_of_le_right (by norm_num) this
        have h4 : 2^12 = 4096 := by norm_num
        linarith [h3, h4]
      omega
    have h6 : y ≤ 5 := by
      by_contra h7
      push_neg at h7
      have h8 : y ≥ 6 := by linarith
      have h9 : 4 ^ y ≥ 4096 := by
        have h10 : y ≥ 6 := h8
        have h11 : 4 ^ y ≥ 4 ^ 6 := by
          apply Nat.pow_le_pow_of_le_right
          all_goals norm_num
          all_goals linarith
        have h12 : 4 ^ 6 = 4096 := by norm_num
        linarith [h11, h12]
      have h10 : 3 * (4 ^ y) ≥ 12288 := by
        omega
      have h11 : 2^x + 3 * (4 ^ y) ≥ 12288 := by
        have h12 : 3 * (4 ^ y) ≥ 12288 := h10
        have h13 : 2^x ≥ 0 := by positivity
        linarith
      omega
    interval_cases y <;> interval_cases x <;> norm_num at h ⊢
    <;> tauto
  · -- Assume (x = 11 ∧ y = 2), prove 2^x + 3 * 4^y = 2096
    rintro ⟨hx, hy⟩
    rw [hx, hy]
    all_goals norm_num