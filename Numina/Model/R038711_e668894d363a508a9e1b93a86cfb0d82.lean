import Mathlib

theorem algebra_17204 {x : ℕ} (hx : x = 7 * 24 * 48) :
    IsLeast {y | 0 < y ∧ ∃ z, z^3 = x * y} 588 := by 
  constructor 
  · -- Verify that 588 is in the set.
    constructor 
    · norm_num
    · -- Show existence of z
      use 168
      rw [hx]
      all_goals
      norm_num
  · -- Show that 588 is the smallest element in the set.
    intro y hy
    rcases hy with ⟨hy_pos, ⟨z, hz⟩⟩
    rw [hx] at hz
    by_contra h
    push_neg at h
    have h1 : z^3 = 7 * 24 * 48 * y := by
      linarith
    have h2 : z ≤ 167 := by
      by_contra h
      push_neg at h
      have h3 : (168) ^ 3 ≤ z ^ 3 := by
        have h4 : 168 ≤ z := by linarith
        have h5 : (168 : ℕ) ^ 3 ≤ (z : ℕ) ^ 3 := by
          apply Nat.pow_le_pow_of_le_left 
          linarith
        linarith
      nlinarith [show (168 : ℕ) ^ 3 > 7 * 24 * 48 * y by nlinarith]
    interval_cases z <;> norm_num [h1] at *
    <;> omega