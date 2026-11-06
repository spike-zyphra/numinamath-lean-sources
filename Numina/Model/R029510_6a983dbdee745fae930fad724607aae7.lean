import Mathlib

theorem algebra_13134 :
  {x : ℝ | x ≠ 3 ∧ x ^ 2 / (x - 3) ^ 2 ≥ 0} = Set.Iio 3 ∪ Set.Ioi 3 := by 
  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
  constructor 
  · -- Assume x in left side, prove right side
    rintro ⟨hx1, hx2⟩
    by_cases h : x < 3 
    · -- x < 3 
      left 
      exact h 
    · -- Not x < 3, so x ≥ 3 
      have h2 : x ≥ 3 := by linarith 
      have h3 : x > 3 := by 
        by_contra h4 
        push_neg at h4 
        have h4' : x = 3 := by linarith 
        contradiction 
      right 
      linarith 
  · -- Assume x in right side, prove left side 
    rintro (h | h)
    · -- Case x < 3 
      have hx1 : x < 3 := h 
      have hxne : x ≠ 3 := by linarith 
      constructor 
      · exact hxne 
      · -- Show x^2/(x-3)^2 ≥ 0 
        have h2 : x - 3 ≠ 0 := by 
          by_contra h3 
          have h4 : x = 3 := by linarith 
          linarith 
        have h3 : x ^ 2 ≥ 0 := by 
          apply sq_nonneg 
        have h4 : (x - 3) ^ 2 > 0 := by 
          apply pow_two_pos_of_ne_zero 
          exact h2 
        apply div_nonneg 
        · linarith 
        · nlinarith 
    · -- Case x > 3 
      have hx2 : x > 3 := h 
      have hxne : x ≠ 3 := by linarith 
      constructor 
      · exact hxne 
      · -- Show x^2/(x-3)^2 ≥ 0 
        have h2 : x - 3 ≠ 0 := by 
          by_contra h3 
          have h4 : x = 3 := by linarith 
          nlinarith 
        have h3 : x ^ 2 ≥ 0 := by 
          apply sq_nonneg 
        have h4 : (x - 3) ^ 2 > 0 := by 
          apply pow_two_pos_of_ne_zero 
          exact h2 
        apply div_nonneg 
        · linarith 
        · nlinarith