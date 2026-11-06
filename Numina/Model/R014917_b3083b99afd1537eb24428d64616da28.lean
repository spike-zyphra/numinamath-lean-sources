import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_319192 {x : ℝ} (hx : x^2 - 6 * x + 8 > 0) :
    (x + 3) / (x - 1) - 2 > 0 ↔ x ∈ Ioo 1 2 ∪ Ioo 4 5 := by
  constructor
  · -- Assume (x + 3) / (x - 1) - 2 > 0, prove x ∈ Ioo 1 2 ∪ Ioo 4 5
    intro h
    have h1 : (x + 3) / (x - 1) - 2 > 0 := h
    have h2 : x - 1 ≠ 0 := by
      by_contra h2
      have : x = 1 := by linarith
      rw [this] at h1
      norm_num at h1 
    have h3 : (5 - x) / (x - 1) > 0 := by 
      have h4 : (x + 3) / (x - 1) - 2 = (5 - x) / (x - 1) := by
        have h5 : x - 1 ≠ 0 := h2
        field_simp
        <;> ring
      linarith [h4, h1]
    have h4 : (1 < x ∧ x < 5) := by
      apply div_pos_iff.mp at h3
      cases h3 with
      | inl h7 =>
        constructor <;> linarith
      | inr h7 =>
        linarith
    have h5 : 1 < x := h4.1
    have h6 : x < 5 := h4.2
    by_cases h7 : x < 2
    · -- Case where x < 2
      have h8 : x ∈ Ioo (1 : ℝ) (2 : ℝ) := ⟨by linarith, by linarith⟩
      left
      simp [h8]
    · -- Case where x ≥ 2
      have h8 : 4 < x := by
        by_contra h9
        push_neg at h9
        have h10 : x^2 - 6 * x + 8 ≤ (0 : ℝ) := by
          nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 4)]
        linarith [h10, hx]
      have h9 : x < 5 := h6
      have h10 : x ∈ Ioo (4 : ℝ) (5 : ℝ) := ⟨by linarith, by linarith⟩
      right
      simp [h10]
  · -- Assume x ∈ Ioo 1 2 ∪ Ioo 4 5, prove (x + 3) / (x - 1) - 2 > 0
    intro h
    rcases h with (h1 | h2)
    · -- Case where x ∈ (1, 2)
      rcases h1 with ⟨h11, h12⟩
      have h2 : x - 1 > 0 := by linarith
      have h3 : 5 - x > 0 := by linarith
      have h4 : (5 - x) / (x - 1) > 0 := by
        apply div_pos
        all_goals linarith
      have h5 : (x + 3) / (x - 1) - 2 = (5 - x) / (x - 1) := by
        have h6 : x - 1 > 0 := h2
        field_simp
        <;> ring
      linarith [h5, h4]
    · -- Case where x ∈ (4, 5)
      rcases h2 with ⟨h21, h22⟩
      have h2 : x - 1 > 0 := by linarith
      have h3 : 5 - x > 0 := by linarith
      have h4 : (5 - x) / (x - 1) > 0 := by
        apply div_pos
        all_goals linarith
      have h5 : (x + 3) / (x - 1) - 2 = (5 - x) / (x - 1) := by
        have h6 : x - 1 > 0 := h2
        field_simp
        <;> ring
      linarith [h5, h4]