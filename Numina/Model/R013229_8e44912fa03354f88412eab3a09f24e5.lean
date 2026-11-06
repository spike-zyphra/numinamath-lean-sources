import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_170228 :
  IsLeast {t : ℝ | ∃ x y : ℝ, x ∈ Icc 0 1 ∧ y ∈ Icc 0 1 ∧ x ≤ y ∧ t = max (max (x * y) (1 - x - y + x * y)) (x + y - 2 * x * y)} (4 / 9) := by
  constructor
  · -- Show 4/9 is achievable, with x=y=2/3
    use 2 / 3, 2 / 3
    constructor
    · -- Show 2/3 ∈ [0, 1]
      norm_num [mem_Icc]
    constructor
    · -- Show 2/3 ∈ [0, 1]
      norm_num [mem_Icc]
    constructor
    · -- Show 2/3 ≤ 2/3
      norm_num
    norm_num [mem_Icc, max_eq_left_of_lt, max_eq_right_of_lt]
  · -- Show 4/9 is the least element
    intro t ht
    rcases ht with ⟨x, y, hx, hy, hxy, ht⟩
    norm_num [mem_Icc] at hx hy
    by_contra h
    push_neg at h
    have ht' : max (max (x * y) (1 - x - y + x * y)) (x + y - 2 * x * y) < 4 / 9 := by
      linarith
    have h1 : x * y < 4 / 9 := by
      have h3 : max (x * y) (1 - x - y + x * y) < 4 / 9 := by
        have h3 : max (max (x * y) (1 - x - y + x * y)) (x + y - 2 * x * y) < 4 / 9 := ht'
        cases max_cases (max (x * y) (1 - x - y + x * y)) (x + y - 2 * x * y) with
        | inl h4 =>
          linarith [h4]
        | inr h4 =>
          nlinarith
      cases max_cases (x * y) (1 - x - y + x * y) with
      | inl h2 =>
        linarith [h2]
      | inr h2 =>
        linarith [h2]
    have h2 : 1 - x - y + x * y < 4 / 9 := by
      have h3 : max (x * y) (1 - x - y + x * y) < 4 / 9 := by
        have h3 : max (max (x * y) (1 - x - y + x * y)) (x + y - 2 * x * y) < 4 / 9 := ht'
        cases max_cases (max (x * y) (1 - x - y + x * y)) (x + y - 2 * x * y) with
        | inl h4 =>
          linarith [h4]
        | inr h4 =>
          nlinarith
      cases max_cases (x * y) (1 - x - y + x * y) with
      | inl h2 =>
        linarith [h2]
      | inr h2 =>
        linarith [h2]
    have h3 : x + y - 2 * x * y < 4 / 9 := by
      have h4 : max (max (x * y) (1 - x - y + x * y)) (x + y - 2 * x * y) < 4 / 9 := ht'
      cases max_cases (max (x * y) (1 - x - y + x * y)) (x + y - 2 * x * y) with
      | inl h4 =>
        nlinarith [show x * y ≥ 0 by nlinarith, show 1 - x - y + x * y ≥ 0 by nlinarith]
      | inr h4 =>
        linarith
    nlinarith [sq_nonneg (x - 2 / 3), sq_nonneg (y - 2 / 3), sq_nonneg (x - y), mul_nonneg (show 0 ≤ y - x by nlinarith) (show 0 ≤ x by nlinarith), mul_nonneg (show 0 ≤ 1 - y by nlinarith) (show 0 ≤ y - x by nlinarith), mul_nonneg (show 0 ≤ x by nlinarith) (show 0 ≤ 1 - x by nlinarith)]