import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_307367 {M : Set ℝ} (hM : M = {x | (x - 5) / (x + 1) < 0}) :
    (MeasureTheory.volume {x | x ∈ M ∧ logb 2 (x + 1) < 1}).toReal =
    (MeasureTheory.volume M).toReal * (1 / 3) := by

  have h1 : M = Ioo (-1) 5 := by
    ext x
    simp [hM]
    constructor
    · -- Show that if (x - 5) / (x + 1) < 0, then x ∈ (-1, 5)
      intro h
      have h1 : x + 1 ≠ 0 := by
        by_contra h2
        have : x = -1 := by linarith
        rw [this] at h
        norm_num at h <;> all_goals linarith
      have h2 : (x - 5) * (x + 1) < 0 := by
        have : (x - 5) / (x + 1) < 0 := h
        apply div_neg_iff.mp at this
        cases this with
        | inl h1 =>
          nlinarith
        | inr h2 =>
          nlinarith
      by_cases h3 : x + 1 > 0
      · -- If x + 1 > 0, then x > -1 and x < 5
        have h4 : x - 5 < 0 := by nlinarith
        constructor <;> linarith
      · -- x + 1 ≤ 0
        have h3 : x + 1 < 0 := by
          by_contra h4
          push_neg at h4
          have : x + 1 = 0 := by linarith
          contradiction
        have h4 : x - 5 > 0 := by nlinarith
        linarith
    · -- Show that if x ∈ (-1, 5), then (x - 5) / (x + 1) < 0
      rintro ⟨h1, h2⟩
      have h3 : x + 1 > 0 := by linarith
      have h4 : x - 5 < 0 := by linarith
      have h5 : (x - 5) / (x + 1) < 0 := by
        apply div_neg_of_neg_of_pos
        linarith
        linarith
      exact h5

  have h2 : {x | x ∈ M ∧ logb 2 (x + 1) < 1} = Ioo (-1) 1 := by
    ext x
    simp [h1]
    constructor
    · -- Show that if x ∈ M and logb 2 (x + 1) < 1, then x ∈ (-1, 1)
      intro h
      rcases h with ⟨⟨hx1, hx2⟩, hlog⟩
      have h1 : x + 1 > 0 := by linarith
      have h2 : x + 1 < 2 := by
        have h3 : logb 2 (x + 1) < 1 := hlog
        have h4 : logb 2 (2 : ℝ) = 1 := by
          rw [logb_self_eq_one]
          all_goals linarith
        have h5 : logb 2 (x + 1) < logb 2 (2 : ℝ) := by linarith [h3, h4]
        have h6 : (2 : ℝ) > 0 := by norm_num
        have h7 : x + 1 > 0 := h1
        have h8 : x + 1 < (2 : ℝ) := by
          apply (logb_lt_logb_iff (by linarith) (by linarith) (by linarith)).mp at h5
          linarith
        linarith
      constructor <;> linarith
    · -- Show that if x ∈ (-1, 1), then x ∈ M and logb 2 (x + 1) < 1
      rintro ⟨h1, h2⟩
      constructor
      · -- Show that x ∈ M
        constructor <;> linarith
      · -- Show that logb 2 (x + 1) < 1
        have h1 : x + 1 > 0 := by linarith
        have h4 : logb 2 (x + 1) < 1 := by
          have h5 : logb 2 (2 : ℝ) = 1 := by
            rw [logb_self_eq_one]
            all_goals linarith
          have h6 : logb 2 (x + 1) < logb 2 (2 : ℝ) := by
            have h6 : (2 : ℝ) > 0 := by norm_num
            have h7 : x + 1 > 0 := h1
            have h8 : x + 1 < (2 : ℝ) := by linarith
            apply (logb_lt_logb_iff (by linarith) (by linarith) (by linarith)).mpr
            linarith
          linarith [h6, h5]
        exact h4

  rw [h2]
  rw [h1]
  simp
  <;> norm_num
  <;> ring_nf <;> norm_num
  all_goals norm_num