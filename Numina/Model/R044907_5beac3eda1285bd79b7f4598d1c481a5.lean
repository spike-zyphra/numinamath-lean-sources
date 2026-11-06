import Mathlib

theorem algebra_10446 :
    {x : ℝ | x + 27 ≠ 0} = Set.Iio (-27) ∪ Set.Ioi (-27) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
  constructor
  · -- Assume x + 27 ≠ 0, prove x ∈ (-∞, -27) ∪ (-27, ∞)
    intro h
    by_cases h1 : x < -27
    · -- If x < -27
      left
      exact h1
    · -- If x ≥ -27
      have h2 : x ≥ -27 := by nlinarith 
      have h3 : x > -27 := by
        by_contra h4
        push_neg at h4 
        have h4' : x = -27 := by linarith 
        have h4'' : x + 27 = (0 : ℝ) := by linarith
        contradiction
      right
      exact h3
  · -- Assume x ∈ (-∞, -27) ∪ (-27, ∞), prove x + 27 ≠ 0
    rintro (h | h)
    · -- If x < -27 
      intro h1
      have : x = -27 := by linarith 
      nlinarith 
    · -- If x > -27 
      intro h1
      have : x = -27 := by linarith 
      nlinarith