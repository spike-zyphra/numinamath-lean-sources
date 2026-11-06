import Mathlib

theorem algebra_309389 (x : ℝ) (hx : x ≠ -2 ∧ x ≠ -3 ∧ x ≠ -8 ∧ x ≠ -9) :
    (x + 1) / (x + 2) + (x + 8) / (x + 9) = (x + 2) / (x + 3) + (x + 7) / (x + 8) ↔
    x = -11 / 2 := by

  constructor
  · -- Forward implication: if the equation holds, then x = -11/2
    intro h
    rcases hx with ⟨hx1, hx2, hx3, hx4⟩
    have h1 : x + 2 ≠ 0 := by
      intro h1
      apply hx1
      linarith
    have h2 : x + 3 ≠ 0 := by
      intro h2
      apply hx2
      linarith
    have h3 : x + 8 ≠ 0 := by
      intro h3
      apply hx3
      linarith
    have h4 : x + 9 ≠ 0 := by
      intro h4
      apply hx4
      linarith
    have eq6 : (x + 1) / (x + 2) - (x + 2) / (x + 3) = (x + 7) / (x + 8) - (x + 8) / (x + 9) := by
      linarith [h]
    have eq7 : ((x + 1) / (x + 2) - (x + 2) / (x + 3)) = -1 / ((x + 2) * (x + 3)) := by 
      field_simp [(show x + 2 ≠ 0 by assumption), (show x + 3 ≠ 0 by assumption)]
      <;> ring
    have eq8 : ((x + 7) / (x + 8) - (x + 8) / (x + 9)) = -1 / ((x + 8) * (x + 9)) := by
      field_simp [(show x + 8 ≠ 0 by assumption), (show x + 9 ≠ 0 by assumption)]
      <;> ring
    rw [eq7, eq8] at eq6
    have eq9 : (x + 8) * (x + 9) = (x + 2) * (x + 3) := by
      field_simp [(show x + 2 ≠ 0 by assumption), (show x + 3 ≠ 0 by assumption),
        (show x + 8 ≠ 0 by assumption), (show x + 9 ≠ 0 by assumption)] at eq6 ⊢
      linarith
    linarith [eq9]
  · -- Backward implication: if x = -11/2, then the equation holds
    intro h
    rw [h]
    norm_num
    <;> field_simp
    <;> norm_num