import Mathlib

theorem calculus_125564 (ε : ℝ) (hε : ε > 0) :
    ∃ δ, δ > 0 ∧ ∀ x, (x ∈ Set.Ioo 3 (3 + δ) ∨ x ∈ Set.Ioo (3 - δ) 3) →
    abs ((4 * x ^ 2 - 14 * x + 6) / (x - 3) - 10) < ε := by
  use ε / 4
  constructor
  · -- Show δ > 0
    linarith
  · -- For any x, if x ∈ (3, 3 + δ) ∪ (3 - δ, 3), then |(4x^2 - 14x + 6) / (x - 3) - 10| < ε
    intro x h
    rcases h with h_right | h_left
    -- Case 1: x ∈ (3, 3 + δ)
    ·
      rcases h_right with ⟨h1, h2⟩
      have h3 : x - 3 > 0 := by linarith
      -- Show that (4x^2 - 14x + 6) / (x - 3) = 4x - 2
      have h4 : (4 * x ^ 2 - 14 * x + 6) / (x - 3) = 4 * x - 2 := by
        have hx : x - 3 ≠ 0 := by linarith
        field_simp [hx]
        ring
      -- Show that |(4x^2 - 14x + 6) / (x - 3) - 10| = |4(x - 3)|
      have h5 : ((4 * x ^ 2 - 14 * x + 6) / (x - 3) - 10) = 4 * (x - 3) := by
        rw [h4]
        have h7 : (4 * x - 2 : ℝ) - 10 = 4 * (x - 3) := by
          ring_nf
        linarith [h7]
      -- Therefore, |4(x - 3)| < 4*(ε / 4) = ε
      have h8 : abs ((4 * x ^ 2 - 14 * x + 6) / (x - 3) - 10) = abs (4 * (x - 3)) := by
        rw [h5]
      rw [h8]
      have h7 : abs (4 * (x - 3)) = 4 * (x - 3) := by
        apply abs_of_pos
        nlinarith
      rw [h7]
      nlinarith
    · 
      rcases h_left with ⟨h1, h2⟩
      have h3 : x - 3 < 0 := by linarith
      -- Show that (4x^2 - 14x + 6) / (x - 3) = 4x - 2
      have h4 : (4 * x ^ 2 - 14 * x + 6) / (x - 3) = 4 * x - 2 := by
        have hx : x - 3 ≠ 0 := by linarith
        field_simp [hx]
        ring
      -- Show that |(4x^2 - 14x + 6) / (x - 3) - 10| = |4(x - 3)|
      have h5 : ((4 * x ^ 2 - 14 * x + 6) / (x - 3) - 10) = 4 * (x - 3) := by
        rw [h4]
        have h7 : (4 * x - 2 : ℝ) - 10 = 4 * (x - 3) := by
          ring_nf
        linarith [h7]
      -- Therefore, |4(x - 3)| < 4*(ε / 4) = ε
      have h8 : abs ((4 * x ^ 2 - 14 * x + 6) / (x - 3) - 10) = abs (4 * (x - 3)) := by
        rw [h5]
      rw [h8]
      have h7 : abs (4 * (x - 3)) = 4 * abs (x - 3) := by
        simp [abs_mul]
        all_goals nlinarith
      rw [h7]
      have h6 : abs (x - 3) < ε / 4 := by
        have h10 : abs (x - 3) = (3 - x) := by
          rw [abs_of_neg]
          nlinarith
          all_goals nlinarith
        rw [h10]
        have h7 : 3 - x < ε / 4 := by linarith
        nlinarith
      nlinarith