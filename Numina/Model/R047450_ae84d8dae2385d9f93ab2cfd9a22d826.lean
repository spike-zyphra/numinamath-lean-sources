import Mathlib

theorem calculus_137326 (ε : ℝ) (hε : ε > 0) :
    ∃ δ, δ > 0 ∧ ∀ x, (x ∈ Set.Ioo (-1 / 2 - δ) (-1 / 2) ∨ x ∈ Set.Ioo (-1 / 2) (-1 / 2 + δ)) →
    abs ((6 * x ^ 2 + x - 1) / (x + 1 / 2) + 5) < ε := by

  use ε / 6
  constructor
  · -- Show δ > 0
    linarith
  · -- Show the implication holds
    intro x h
    rcases h with (h | h)
    · -- Case where x ∈ (-1/2 - δ, -1/2)
      rcases h with ⟨h1, h2⟩
      have h3 : x + 1 / 2 < 0 := by linarith
      have h4 : abs (x + 1 / 2) < ε / 6 := by
        rw [abs_of_neg h3]
        linarith
      have h8 : (6 * x ^ 2 + x - 1) / (x + 1 / 2) = 2 * (3 * x - 1) := by
        have h9 : x + 1 / 2 ≠ 0 := by
          linarith
        have h11 : (6 * x ^ 2 + x - 1) = (2 * (3 * x - 1)) * (x + 1 / 2) := by 
          ring_nf 
        rw [h11]
        have h99 : (2 * (3 * x - 1)) * (x + 1 / 2) / (x + 1 / 2) = 2 * (3 * x - 1) := by 
          have h100 : x + 1 / 2 ≠ 0 := h9 
          rw [mul_div_cancel_right₀ _ h100]
        linarith 
      have h7 : abs ((6 * x ^ 2 + x - 1) / (x + 1 / 2) + 5) < ε := by
        rw [show (6 * x ^ 2 + x - 1) / (x + 1 / 2) + 5 = (2 * (3 * x - 1) + 5) by rw [h8]]
        have h9 : abs ((2 * (3 * x - 1) + 5)) = 6 * abs (x + 1 / 2) := by
          have h10 : (2 * (3 * x - 1) + 5) = 6 * (x + 1 / 2) := by 
            linarith
          rw [h10]
          have h11 : abs (6 * (x + 1 / 2)) = 6 * abs (x + 1 / 2) := by 
            rw [abs_mul]
            norm_num
          linarith
        rw [h9] at *
        linarith
      linarith 
    · -- Case where x ∈ (-1/2, -1/2 + δ)
      rcases h with ⟨h1, h2⟩
      have h3 : x + 1 / 2 > 0 := by linarith
      have h4 : abs (x + 1 / 2) < ε / 6 := by
        rw [abs_of_pos h3]
        linarith
      have h8 : (6 * x ^ 2 + x - 1) / (x + 1 / 2) = 2 * (3 * x - 1) := by
        have h9 : x + 1 / 2 ≠ 0 := by
          linarith
        have h11 : (6 * x ^ 2 + x - 1) = (2 * (3 * x - 1)) * (x + 1 / 2) := by 
          ring_nf 
        rw [h11]
        have h99 : (2 * (3 * x - 1)) * (x + 1 / 2) / (x + 1 / 2) = 2 * (3 * x - 1) := by 
          have h100 : x + 1 / 2 ≠ 0 := h9 
          rw [mul_div_cancel_right₀ _ h100]
        linarith 
      have h7 : abs ((6 * x ^ 2 + x - 1) / (x + 1 / 2) + 5) < ε := by
        rw [show (6 * x ^ 2 + x - 1) / (x + 1 / 2) + 5 = (2 * (3 * x - 1) + 5) by rw [h8]]
        have h9 : abs ((2 * (3 * x - 1) + 5)) = 6 * abs (x + 1 / 2) := by
          have h10 : (2 * (3 * x - 1) + 5) = 6 * (x + 1 / 2) := by 
            linarith
          rw [h10]
          have h11 : abs (6 * (x + 1 / 2)) = 6 * abs (x + 1 / 2) := by 
            rw [abs_mul]
            norm_num
          linarith
        rw [h9] at *
        linarith
      linarith