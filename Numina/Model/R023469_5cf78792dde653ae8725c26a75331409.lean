import Mathlib

open Real Set

theorem algebra_318256 :
    IsLeast {x | ∃ a b : ℝ, x = max (max (|a + b|) (|a - b|)) (max (|1 - a|) (|1 - b|))} (2 / 3) := by

  constructor
  · -- Show 2/3 is in the set.
    use 1 / 3, 1 / 3
    norm_num [abs_of_pos, abs_of_neg, max_eq_left, max_eq_right]
    all_goals norm_num
  · -- Show 2/3 is the least element in the set.
    intro x hx
    rcases hx with ⟨a, b, hx⟩
    have h1 : max (max (|a + b|) (|a - b|)) (max (|1 - a|) (|1 - b|)) ≥ 2 / 3 := by
      by_contra h
      push_neg at h
      have h2 : max (max (|a + b|) (|a - b|)) (max (|1 - a|) (|1 - b|)) < 2 / 3 := by linarith
      have h3 : max (|a + b|) (|a - b|) < 2 / 3 := by
        cases max_cases (max (|a + b|) (|a - b|)) (max (|1 - a|) (|1 - b|)) with
        | inl h21 =>
          linarith
        | inr h22 =>
          cases max_cases (|1 - a|) (|1 - b|) with
          | inl h11 =>
            linarith
          | inr h12 =>
            linarith
      have h5 : |a + b| < 2 / 3 := by
        cases max_cases (|a + b|) (|a - b|) with
        | inl h7 =>
          linarith
        | inr h8 =>
          linarith
      have h6 : |a - b| < 2 / 3 := by
        cases max_cases (|a + b|) (|a - b|) with
        | inl h7 =>
          linarith
        | inr h8 =>
          linarith
      have h7 : max (|1 - a|) (|1 - b|) < 2 / 3 := by
        cases max_cases (max (|a + b|) (|a - b|)) (max (|1 - a|) (|1 - b|)) with
        | inl h8 =>
          cases max_cases (|a + b|) (|a - b|) with
          | inl h9 =>
            linarith
          | inr h10 =>
            linarith
        | inr h11 =>
          linarith
      have h8 : |1 - a| < 2 / 3 := by
        cases max_cases (|1 - a|) (|1 - b|) with
        | inl h9 =>
          linarith
        | inr h10 =>
          linarith
      have h9 : |1 - b| < 2 / 3 := by
        cases max_cases (|1 - a|) (|1 - b|) with
        | inl h10 =>
          linarith
        | inr h11 =>
          linarith
      have h10 : -2 / 3 < a + b := by
        linarith [abs_lt.mp h5]
      have h11 : a + b < 2 / 3 := by
        linarith [abs_lt.mp h5]
      have h12 : -2 / 3 < a - b := by
        linarith [abs_lt.mp h6]
      have h13 : a - b < 2 / 3 := by
        linarith [abs_lt.mp h6]
      have h14 : -2 / 3 < 1 - a := by
        linarith [abs_lt.mp h8]
      have h15 : 1 - a < 2 / 3 := by
        linarith [abs_lt.mp h8]
      have h16 : -2 / 3 < 1 - b := by
        linarith [abs_lt.mp h9]
      have h17 : 1 - b < 2 / 3 := by
        linarith [abs_lt.mp h9]
      linarith
    linarith [h1, hx]