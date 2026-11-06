import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_229240 (x : ℝ) :
  x * cos x - 1 < x - cos x ↔ x > -1 ∧ ¬∃ k : ℤ, x = 2 * k * π := by
  constructor
  · -- Assume the inequality holds, need to prove x > -1 ∧ ¬∃ k : ℤ, x = 2 * k * π
    intro h
    have h1 : (x + 1) * (cos x - 1) < 0 := by
      nlinarith [h, Real.cos_le_one x, Real.neg_one_le_cos x, Real.cos_le_one x]
    have h2 : x + 1 > 0 := by
      nlinarith [show cos x - 1 ≤ 0 by linarith [Real.cos_le_one x], show cos x - 1 ≥ -2 by nlinarith [Real.neg_one_le_cos x, Real.cos_le_one x], h1]
    have h3 : x > -1 := by linarith
    have h4 : ¬∃ k : ℤ, x = 2 * k * π := by
      by_contra h
      rcases h with ⟨k, hk⟩
      have hcos : cos x = 1 := by
        rw [hk]
        have : cos (2 * (k : ℝ) * π) = 1 := by
          have h1 : 2 * (k : ℝ) * π = (k : ℝ) * (2 * π) := by 
            ring_nf
          rw [h1]
          rw [Real.cos_int_mul_two_pi]
        linarith
      have h5 : cos x - 1 = 0 := by
        linarith [hcos]
      have h6 : (x + 1) * (cos x - 1) = 0 := by
        rw [h5]
        norm_num
      nlinarith [h6, h1]
    constructor
    · linarith
    · exact h4
  · -- Assume x > -1 ∧ ¬∃ k : ℤ, x = 2 * k * π, need to prove the inequality
    rintro ⟨h_x_pos, h_ne⟩
    have h1 : x + 1 > 0 := by linarith
    have h2 : cos x - 1 < 0 := by
      by_contra h
      push_neg at h
      have h4 : cos x = 1 := by
        linarith [Real.cos_le_one x, h]
      have h5 : ∃ k : ℤ, x = 2 * k * π := by
        rw [Real.cos_eq_one_iff] at h4
        rcases h4 with ⟨k, hk⟩
        refine ⟨k, by linarith⟩
      have h6 : ∃ k : ℤ, x = 2 * k * π := h5
      have h7 : ¬∃ k : ℤ, x = 2 * k * π := h_ne
      contradiction
    have h3 : (x + 1) * (cos x - 1) < 0 := by
      apply mul_neg_of_pos_of_neg
      · linarith
      · linarith
    have h4 : x * cos x - 1 < x - cos x := by
      nlinarith
      all_goals nlinarith [Real.cos_le_one x, Real.neg_one_le_cos x]
    linarith