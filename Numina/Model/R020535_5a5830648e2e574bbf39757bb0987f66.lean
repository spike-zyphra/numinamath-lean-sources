import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_327062 {f : ℝ → ℝ}
  (hf : f = λ x => max (abs (x + 1)) (abs (x^2 - 5))) :
  IsLeast (range f) 1 := by
  constructor
  · -- Show that 1 is in the range of f
    use -2
    rw [hf]
    norm_num [abs_of_nonneg, abs_of_nonpos, max_eq_left, max_eq_right]
    all_goals norm_num
  · -- Show that 1 is the least element in the range of f
    intro y
    rintro ⟨x, hx⟩
    rw [hf] at hx
    simp at hx
    by_contra h
    push_neg at h
    have h1 : max (abs (x + 1)) (abs (x^2 - 5)) < 1 := by linarith [h, hx]
    have h3 : abs (x + 1) < 1 := by
      by_contra h4
      push_neg at h4
      have h4' : max (abs (x + 1)) (abs (x^2 - 5)) ≥ abs (x + 1) := by
        cases max_cases (abs (x + 1)) (abs (x^2 - 5)) with
        | inl h3 =>
          linarith
        | inr h3 =>
          linarith [show abs (x + 1) ≤ abs (x ^ 2 - 5) by linarith [h3], show abs (x ^ 2 - 5) ≥ abs (x + 1) by linarith [h3]]
      have h5 : abs (x + 1) ≥ 1 := h4
      linarith [h1, h4', h5]
    have h4 : abs (x^2 - 5) < 1 := by
      by_contra h5
      push_neg at h5
      have h6 : max (abs (x + 1)) (abs (x^2 - 5)) ≥ abs (x^2 - 5) := by
        cases max_cases (abs (x + 1)) (abs (x^2 - 5)) with
        | inl h3 =>
          linarith [show abs (x^2 - 5) ≤ abs (x + 1) by linarith [h3], show abs (x + 1) ≥ abs (x^2 - 5) by linarith [h3]]
        | inr h3 =>
          linarith
      have h7 : abs (x^2 - 5) ≥ 1 := h5
      linarith [h1, h6, h7]
    have h8 : -2 < x := by
      linarith [abs_lt.mp h3]
    have h9 : x < 0 := by
      linarith [abs_lt.mp h3]
    have h10 : 4 < x ^ 2 := by
      nlinarith [abs_lt.mp h4]
    nlinarith [abs_nonneg (x + 1), abs_nonneg (x ^ 2 - 5), sq_nonneg (x), sq_nonneg (x + 1), sq_nonneg (x ^ 2 - 5)]