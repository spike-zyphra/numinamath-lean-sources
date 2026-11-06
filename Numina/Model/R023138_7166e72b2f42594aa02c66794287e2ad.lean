import Mathlib

theorem algebra_69446 {a b c : ℝ} (P1 : ℝ → ℝ) (hP1 : P1 = fun x => a * x ^ 2 - b * x - c)
    (P2 : ℝ → ℝ) (hP2 : P2 = fun x => b * x ^ 2 - c * x - a) (P3 : ℝ → ℝ)
    (hP3 : P3 = fun x => c * x ^ 2 - a * x - b) (α : ℝ) (hα : P1 α = P2 α) (hα' : P2 α = P3 α) :
    a = b ∧ b = c := by

  have eq1 : a * α ^ 2 - b * α - c = b * α ^ 2 - c * α - a := by
    rw [hP1] at hα
    rw [hP2] at hα
    simp at hα
    linarith

  have eq2 : b * α ^ 2 - c * α - a = c * α ^ 2 - a * α - b := by
    rw [hP2] at hα'
    rw [hP3] at hα'
    simp at hα'
    linarith

  have eq3 : a * α ^ 2 - b * α - c = c * α ^ 2 - a * α - b := by
    linarith [eq1, eq2]

  have eq4 : (a - b) * α ^ 2 + (c - b) * α + (a - c) = 0 := by 
    linarith [eq1]

  have eq5 : (b - c) * α ^ 2 + (a - c) * α + (b - a) = 0 := by 
    linarith [eq2]

  have eq6 : (a - c) * α ^ 2 + (a - b) * α + (b - c) = 0 := by 
    nlinarith [eq1, eq2, eq3]

  by_cases h : α = 1
  · -- α = 1
    have ha1 : a - b = 0 := by
      rw [h] at eq4 
      linarith 
    have hb1 : b - c = 0 := by
      rw [h] at eq5 
      nlinarith 
    constructor
    · linarith
    · linarith
  · -- α ≠ 1
    have h1 : (a - b) * α ^ 2 + (c - b) * α + (a - c) = 0 := eq4
    have h2 : (b - c) * α ^ 2 + (a - c) * α + (b - a) = 0 := eq5
    have h3 : (a - c) * α ^ 2 + (a - b) * α + (b - c) = 0 := eq6

    have h4 : α - 1 ≠ 0 := by 
      intro h'
      apply h
      linarith

    have ha1 : a - b = 0 := by 
      have h5 : (a - b) * (α - 1) = 0 := by 
        have eq7 : (a - b) * (α - 1) = 0 := by 
          nlinarith [sq_pos_of_ne_zero (show α - 1 ≠ 0 by exact h4), sq_nonneg (α - 1), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), sq_nonneg (α ^ 2 - 1)]
        exact eq7 
      cases (mul_eq_zero.mp h5) with 
      | inl h6 => 
        linarith 
      | inr h7 => 
        exfalso 
        apply h4 
        linarith 
    have hb1 : b - c = 0 := by 
      have h8 : (b - c) * (α - 1) = 0 := by 
        have eq10 : (b - c) * (α - 1) = 0 := by 
          nlinarith [sq_pos_of_ne_zero (show α - 1 ≠ 0 by exact h4), sq_nonneg (α - 1), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), sq_nonneg (α ^ 2 - 1)]
        exact eq10 
      cases (mul_eq_zero.mp h8) with 
      | inl h9 => 
        linarith 
      | inr h10 => 
        exfalso 
        apply h4 
        linarith 
    constructor 
    · linarith 
    · linarith