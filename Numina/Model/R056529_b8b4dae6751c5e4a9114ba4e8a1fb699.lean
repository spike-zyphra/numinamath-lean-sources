import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_90059 (a b c d e : ℝ) (ha : a < b) (hb : b < c) (hc : c < d)
  (hd : d < e) :
  IsLeast {x | ∃ t : ℝ, x = abs (t - a) + abs (t - b) + abs (t - c) + abs (t - d) + abs (t - e)} (-a - b + d + e) := by
  constructor
  · -- Show that -a -b + d + e is achievable by t = c
    use c
    have h1 : c - a > 0 := by linarith
    have h2 : c - b > 0 := by linarith
    have h3 : c - c = (0 : ℝ) := by linarith
    have hcd : d - c > 0 := by linarith
    have hce : e - c > 0 := by linarith
    have h6 : abs (c - a) = c - a := abs_of_pos h1
    have h7 : abs (c - b) = c - b := abs_of_pos h2
    have h8 : abs (c - c) = (0 : ℝ) := by simp
    have h9 : abs (c - d) = d - c := by
      have h10 : c - d < 0 := by linarith
      rw [abs_of_neg h10]
      all_goals linarith
    have h10 : abs (c - e) = e - c := by
      have h11 : c - e < 0 := by linarith
      rw [abs_of_neg h11]
      all_goals linarith
    rw [h6, h7, h8, h9, h10]
    linarith
  · -- Show that it is minimum
    intro x hx
    rcases hx with ⟨t, ht⟩
    -- Compute using the properties of the median
    rw [ht]
    have h1 : abs (t - a) + abs (t - e) ≥ e - a := by
      cases abs_cases (t - a) with
      | inl h1 =>
        cases abs_cases (t - e) with
        | inl h2 =>
          linarith
        | inr h2 =>
          linarith
      | inr h1 =>
        cases abs_cases (t - e) with
        | inl h2 =>
          linarith
        | inr h2 =>
          linarith
    have h2 : abs (t - b) + abs (t - d) ≥ d - b := by
      cases abs_cases (t - b) with
      | inl h1 =>
        cases abs_cases (t - d) with
        | inl h2 =>
          linarith
        | inr h2 =>
          linarith
      | inr h1 =>
        cases abs_cases (t - d) with
        | inl h2 =>
          linarith
        | inr h2 =>
          linarith
    have h3 : abs (t - c) ≥ 0 := abs_nonneg (t - c)
    linarith [h1, h2, h3]