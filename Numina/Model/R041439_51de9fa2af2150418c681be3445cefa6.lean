import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_167904 :
  IsLeast {M | ∃ x y : ℝ, M = max (max (x * y) ((x - 1) * (y - 1))) (x + y - 2 * x * y) ∧
    0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1} (4 / 9) := by 
  constructor
  · -- Show 4/9 is in the set
    use 2/3, 2/3
    norm_num [max_eq_right, max_eq_left]
  · -- Show that any M in the set is ≥ 4/9
    intro M hm
    rcases hm with ⟨x, y, hM, hx1, hx2, hy1, hy2⟩
    by_contra h'
    push_neg at h'
    have h1 : max (max (x * y) ((x - 1) * (y - 1))) (x + y - 2 * x * y) ≥ x * y := by
      have h11 : max (x * y) ((x - 1) * (y - 1)) ≥ x * y := by
        cases max_cases (x * y) ((x - 1) * (y - 1)) with
        | inl h =>
          linarith
        | inr h =>
          linarith
      have h12 : max (max (x * y) ((x - 1) * (y - 1))) (x + y - 2 * x * y) ≥ max (x * y) ((x - 1) * (y - 1)) := by 
        apply le_max_left 
      linarith [h11, h12]
    have h2 : max (max (x * y) ((x - 1) * (y - 1))) (x + y - 2 * x * y) ≥ (x - 1) * (y - 1) := by
      have h21 : max (x * y) ((x - 1) * (y - 1)) ≥ (x - 1) * (y - 1) := by 
        cases max_cases (x * y) ((x - 1) * (y - 1)) with
        | inl h =>
          linarith
        | inr h =>
          linarith
      have h22 : max (max (x * y) ((x - 1) * (y - 1))) (x + y - 2 * x * y) ≥ max (x * y) ((x - 1) * (y - 1)) := by 
        apply le_max_left 
      linarith [h21, h22]
    have h3 : max (max (x * y) ((x - 1) * (y - 1))) (x + y - 2 * x * y) ≥ x + y - 2 * x * y := by 
      apply le_max_right 
    have h4 : x * y < 4 / 9 := by 
      linarith [hM, h1, h']
    have h5 : (x - 1) * (y - 1) < 4 / 9 := by 
      linarith [hM, h2, h']
    have h6 : x + y - 2 * x * y < 4 / 9 := by 
      linarith [hM, h3, h']
    -- With endpoints x and y in [0,1], M is bounded below by 4/9 due to endpoints (x=y=2/3) representing minimum.
    nlinarith [sq_nonneg (x - 2 / 3), sq_nonneg (y - 2 / 3), 
      sq_nonneg (x - y), 
      mul_nonneg (show (0:ℝ) ≤ x by linarith) (show (0:ℝ) ≤ 1 - x by linarith), 
      mul_nonneg (show (0:ℝ) ≤ y by linarith) (show (0:ℝ) ≤ 1 - y by linarith), 
      mul_nonneg (show (0:ℝ) ≤ 1 - x by linarith) (show (0:ℝ) ≤ 1 - y by linarith)
    ]