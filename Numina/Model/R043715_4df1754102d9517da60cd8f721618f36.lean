import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_288928 {f g : ℝ → ℝ} :
  {x | f x / g x > 0} = {x | f x * g x > 0} := by 
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · -- Assume f(x) / g(x) > 0, we need to prove f(x) * g x > 0
    intro h
    have h1 : f x / g x > 0 := h
    by_cases h2 : g x > 0
    · -- If g x > 0, then f x > 0
      have h3 : f x > 0 := by
        apply div_pos_iff.mp at h1
        cases h1 with
        | inl h1 =>
          nlinarith
        | inr h1 =>
          linarith
      have h4 : f x * g x > 0 := by
        apply mul_pos
        all_goals linarith
      exact h4
    · -- g x ≤ 0
      by_cases h3 : g x < 0
      · -- If g x < 0, then f x < 0
        have h4 : f x < 0 := by
          apply div_pos_iff.mp at h1
          cases h1 with
          | inl h1 =>
            linarith
          | inr h1 =>
            nlinarith
        have h5 : f x * g x > 0 := by
          apply mul_pos_of_neg_of_neg
          all_goals linarith
        exact h5
      · -- g x ≥ 0, and since it's not > 0 or < 0, so g x = 0
        have h4 : g x = 0 := by
          linarith
        have h5 : f x / g x = 0 := by
          rw [h4]
          norm_num
        linarith -- contradiction with h5 and h1
  · -- Assume f(x) * g x > 0, we need to prove f(x) / g(x) > 0
    intro h
    have h2 : f x * g x > 0 := h
    by_cases h3 : g x > 0
    · -- If g x > 0, then f x > 0
      have h4 : f x > 0 := by
        nlinarith
      have h6 : f x / g x > 0 := by
        apply div_pos
        all_goals linarith
      exact h6
    · -- g x ≤ 0
      by_cases h4 : g x < 0
      · -- If g x < 0, then f x < 0
        have h5 : f x < 0 := by
          nlinarith
        have h6 : f x / g x > 0 := by
          apply div_pos_of_neg_of_neg
          all_goals linarith
        exact h6
      · -- g x ≥ 0, and since it's not > 0 or < 0, so g x = 0
        have h5 : g x = 0 := by
          linarith
        have h6 : f x * g x = 0 := by
          rw [h5]
          norm_num
        linarith -- contradiction with h6 and h2