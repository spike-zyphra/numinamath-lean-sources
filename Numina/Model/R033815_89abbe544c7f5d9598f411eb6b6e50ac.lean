import Mathlib

theorem algebra_12907 :
    IsLeast {x : ℝ | ∃ a b : ℤ, a > b ∧ x > 0 ∧ x = (a + b) / (a - b) + (a - b) / (a + b)} 2 := by
  constructor
  · -- Show 2 is in the set
    use 1, 0
    norm_num
  · -- Show there is no smaller element in the set
    intro x hx
    rcases hx with ⟨a, b, h1, hx1, heq⟩
    have h3 : (a - b : ℝ) > 0 := by
      have h4 : (a : ℝ) > (b : ℝ) := by exact_mod_cast h1
      linarith
    have h5 : (a + b : ℝ) ≠ 0 := by
      by_contra h6
      have h6' : (a + b : ℝ) / (a - b : ℝ) + (a - b : ℝ) / (a + b : ℝ) = (0 : ℝ) := by
        rw [h6]
        norm_num
        <;> nlinarith
      nlinarith [heq, h6', hx1]
    have h6 : (a + b : ℝ) / (a - b : ℝ) + (a - b : ℝ) / (a + b : ℝ) ≥ (2 : ℝ) := by
      have h9 : (a + b : ℝ) ≠ 0 := h5
      have h10 : (a - b : ℝ) > 0 := h3
      have h11 : (a + b : ℝ) > 0 := by
        by_contra h7
        push_neg at h7
        have h8 : (a + b : ℝ) < (0 : ℝ) := by
          by_contra h9
          push_neg at h9
          have : (a + b : ℝ) = 0 := by linarith
          contradiction
        have h100 : (a + b : ℝ) / (a - b : ℝ) + (a - b : ℝ) / (a + b : ℝ) < (0 : ℝ) := by
          have h7 : (a + b : ℝ) < (0 : ℝ) := h8
          have h8 : (a - b : ℝ) > 0 := h3
          have h9 : (a + b : ℝ) / (a - b : ℝ) < (0 : ℝ) := by
            apply div_neg_of_neg_of_pos
            . linarith
            . linarith
          have h10 : (a - b : ℝ) / (a + b : ℝ) < (0 : ℝ) := by
            apply div_neg_of_pos_of_neg
            . linarith
            . linarith
          linarith
        nlinarith [h100, heq, hx1]
      have h7 : (a + b : ℝ) / (a - b : ℝ) + (a - b : ℝ) / (a + b : ℝ) - (2 : ℝ) ≥ 0 := by
        have h8 : (a + b : ℝ) / (a - b : ℝ) + (a - b : ℝ) / (a + b : ℝ) - (2 : ℝ) = 
          ((a + b : ℝ)^2 + (a - b : ℝ)^2 - 2 * ((a - b : ℝ) * (a + b : ℝ)) ) / ((a - b : ℝ) * (a + b : ℝ)) := by
          field_simp [(show (a - b : ℝ) ≠ 0 by linarith), (show (a + b : ℝ) ≠ 0 by exact_mod_cast h5)]
          <;> ring
        rw [h8]
        have h9 : ((a + b : ℝ)^2 + (a - b : ℝ)^2 - 2 * ((a - b : ℝ) * (a + b : ℝ)) ) ≥ 0 := by
          nlinarith [sq_nonneg ((a + b : ℝ) - (a - b : ℝ)), sq_nonneg ((a + b : ℝ) + (a - b : ℝ)), sq_nonneg ((a - b : ℝ) - (a + b : ℝ))]
        have h12 : (a - b : ℝ) * (a + b : ℝ) > 0 := by
          nlinarith [h3, h11]
        apply div_nonneg
        . linarith
        . linarith
      linarith
    nlinarith [heq, h6]