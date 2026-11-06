import Mathlib

theorem algebra_18586 : {x : ℝ | 0 < x ^ 2 - 5 * x + 6} = Set.Iio 2 ∪ Set.Ioi 3 := by 
  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
  constructor
  · -- Assume 0 < x^2 - 5 * x + 6, prove x < 2 or x > 3
    intro h
    have h1 : x ^ 2 - 5 * x + 6 > 0 := by linarith 
    have h2 : (x - 2) * (x - 3) > 0 := by nlinarith 
    by_cases h3 : x < 2
    · -- If x < 2, then it's in the left side of the union 
      left 
      assumption 
    · -- Assume x ≥ 2 
      have h4 : x ≥ 2 := by linarith 
      have h5 : x > 3 := by 
        nlinarith 
      right 
      linarith 
  · -- Assume x < 2 or x > 3, prove 0 < x^2 - 5 * x + 6 
    rintro (h | h)
    · -- Assume x < 2 
      have h4 : x < 2 := by linarith 
      nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 3)]
    · -- Assume x > 3 
      have h5 : x > 3 := by linarith 
      nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 3)]