import Mathlib

open Real

theorem inequalities_290158 (a b c d : ℝ) (h : a + b + c + d = 0) :
    max a b + max a c + max a d + max b c + max b d + max c d ≥ 0 := by

  have h1 : max a b ≥ (a + b) / 2 := by
    cases max_cases a b with
    | inl h2 =>
        linarith
    | inr h2 =>
        linarith

  have h2 : max a c ≥ (a + c) / 2 := by
    cases max_cases a c with
    | inl h2 =>
        linarith
    | inr h2 =>
        linarith

  have h3 : max a d ≥ (a + d) / 2 := by
    cases max_cases a d with
    | inl h2 =>
        linarith
    | inr h2 =>
        linarith

  have h4 : max b c ≥ (b + c) / 2 := by
    cases max_cases b c with
    | inl h2 =>
        linarith
    | inr h2 =>
        linarith

  have h5 : max b d ≥ (b + d) / 2 := by
    cases max_cases b d with
    | inl h2 =>
        linarith
    | inr h2 =>
        linarith

  have h6 : max c d ≥ (c + d) / 2 := by
    cases max_cases c d with
    | inl h2 =>
        linarith
    | inr h2 =>
        linarith

  have h7 : max a b + max a c + max a d + max b c + max b d + max c d ≥
      (a + b)/2 + (a + c)/2 + (a + d)/2 + (b + c)/2 + (b + d)/2 + (c + d)/2 := by
    linarith [h1, h2, h3, h4, h5, h6]

  have h8 : (a + b)/2 + (a + c)/2 + (a + d)/2 + (b + c)/2 + (b + d)/2 + (c + d)/2 = 3/2 * (a + b + c + d) := by
    ring

  have h9 : (a + b)/2 + (a + c)/2 + (a + d)/2 + (b + c)/2 + (b + d)/2 + (c + d)/2 = 0 := by
    rw [h8]
    rw [show a + b + c + d = (0 : ℝ) by linarith]
    norm_num

  linarith [h7, h9]