import Mathlib

theorem algebra_12144 : {x : ℝ | x^2 - 2 * x > 35} = Set.Iio (-5) ∪ Set.Ioi 7 := by 
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
  constructor
  · -- Assume x^2 - 2 * x > 35, prove x ∈ (-∞, -5) ∪ (7, ∞)
    intro h
    have h1 : x^2 - 2 * x - 35 > 0 := by linarith
    have h2 : (x - 7) * (x + 5) > 0 := by 
      nlinarith
    cases mul_pos_iff.mp h2 with
    | inl h3 =>
      right
      linarith
    | inr h4 =>
      left
      linarith
  · -- Assume x ∈ (-∞, -5) ∪ (7, ∞), prove x^2 - 2 * x > 35
    rintro (h | h)
    · -- Case x < -5
      have h1 : x + 5 < 0 := by linarith
      have h2 : x - 7 < 0 := by linarith
      have h3 : (x - 7) * (x + 5) > 0 := by 
        apply mul_pos_of_neg_of_neg
        all_goals linarith
      nlinarith
    · -- Case x > 7
      have h1 : x - 7 > 0 := by linarith
      have h2 : x + 5 > 0 := by linarith
      have h3 : (x - 7) * (x + 5) > 0 := by 
        apply mul_pos
        all_goals linarith
      nlinarith