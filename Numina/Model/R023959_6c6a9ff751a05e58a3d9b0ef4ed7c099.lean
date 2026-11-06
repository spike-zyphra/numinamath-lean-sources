import Mathlib

theorem calculus_138286 (ε : ℝ) (hε : ε > 0) :
    ∃ δ, δ > 0 ∧ ∀ x, (x ∈ Set.Ioo 8 (8 + δ) ∨ x ∈ Set.Ioo (8 - δ) 8) →
    abs ((3 * x ^ 2 - 40 * x + 128) / (x - 8) - 8) < ε := by
  use ε / 3
  constructor
  · -- Show δ > 0
    linarith [hε]
  · -- For all x, if x in the union of the two open intervals, then the inequality holds
    intro x h
    rcases h with (h | h)
    -- Case 1: x ∈ (8, 8 + δ)
    · -- Case where x ∈ (8, 8 + δ)
      rcases h with ⟨hx1, hx2⟩
      have h1 : x - 8 > 0 := by linarith
      have h4 : x - 8 < ε / 3 := by linarith
      have h3 : (3 * x ^ 2 - 40 * x + 128) / (x - 8) = 3 * x - 16 := by
        have h4 : x - 8 ≠ 0 := by linarith
        field_simp [h4]
        ring_nf
      rw [h3]
      have h4 : abs ((3 * x - 16 ) - 8) = abs (3 * (x - 8)) := by
        ring_nf
      rw [h4]
      have h5 : abs (3 * (x - 8)) = 3 * abs (x - 8) := by
        have h6 : abs (3 * (x - 8)) = abs (3) * abs (x - 8) := by
          rw [abs_mul]
        have h7 : abs (3 : ℝ) = 3 := by
          norm_num
        rw [h7] at h6
        linarith [h6]
      rw [h5]
      have h6 : abs (x - 8) < ε / 3 := by
        have h7 : abs (x - 8) = x - 8 := by
          rw [abs_of_pos h1]
        rw [h7]
        linarith
      have h8 : 3 * abs (x - 8) < ε := by
        linarith [h6]
      linarith [h8]
    -- Case 2: x ∈ (8 - δ, 8)
    · -- Case where x ∈ (8 - δ, 8)
      rcases h with ⟨hx1, hx2⟩
      have h1 : x - 8 < 0 := by linarith
      have h4 : 8 - x < ε / 3 := by linarith
      have h3 : (3 * x ^ 2 - 40 * x + 128) / (x - 8) = 3 * x - 16 := by
        have h4 : x - 8 ≠ 0 := by linarith
        field_simp [h4]
        ring_nf
      rw [h3]
      have h4 : abs ((3 * x - 16 ) - 8) = abs (3 * (x - 8)) := by
        ring_nf
      rw [h4]
      have h5 : abs (3 * (x - 8)) = 3 * abs (x - 8) := by
        have h6 : abs (3 * (x - 8)) = abs (3) * abs (x - 8) := by
          rw [abs_mul]
        have h7 : abs (3 : ℝ) = 3 := by
          norm_num
        rw [h7] at h6
        linarith [h6]
      rw [h5]
      have h7 : abs (x - 8) = (8 - x : ℝ) := by
        rw [abs_of_neg (by linarith)]
        linarith
      have h8 : abs (x - 8) < ε / 3 := by
        rw [h7]
        linarith
      have h9 : 3 * abs (x - 8) < ε := by
        linarith [h8]
      linarith [h9]