import Mathlib

/-
Problem

The set ${}x | x^2 - 2x + m = 0\}$ contains two elements. The condition that the real number $m$ must satisfy is __________.
-/

theorem algebra_9462 (m : ℝ) (h : ∃ x y, x ≠ y ∧ x^2 - 2 * x + m = 0 ∧ y^2 - 2 * y + m = 0) :
    m < 1 := by

  rcases h with ⟨x, y, h1, h2, h3⟩

  have h4 : (x - y) * (x + y - 2) = 0 := by
    nlinarith 
  cases' (mul_eq_zero.mp h4) with h5 h6
  · -- x - y = 0 
    exfalso
    apply h1
    linarith
  · -- x + y - 2 = 0
    have h7 : x + y = 2 := by
      linarith

    have eq1 : m = 2 * x - x^2 := by
      nlinarith 
    have eq2 : (x - 1) ^ 2 > 0 := by
      by_contra h8
      push_neg at h8
      have h9 : (x - 1) ^ 2 = 0 := by
        nlinarith [sq_nonneg (x - 1)]
      have h10 : x - 1 = 0 := by
        nlinarith
      have h11 : x = 1 := by
        nlinarith 
      have h12 : y = 1 := by
        nlinarith [h7, h11]
      have h13 : x = y := by
        linarith [h12, h11]
      contradiction

    have eq4 : 1 - m > 0 := by
      nlinarith 
    linarith