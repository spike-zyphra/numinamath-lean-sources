import Mathlib

open Set

theorem Inequalities_170775 (x : ℝ) (hx : x ≠ 0 ∧ x ≠ - 1 ∧ x ≠ 3) 
    (h1 : (2 - x) / (x ^ 3 + x ^ 2) > (1 - 2 * x) / (x ^ 3 - 3 * x ^ 2) ) :
    x ∈ Iio (-7) ∪ Set.Ioo (-1) 0 ∪ Set.Ioo 0 1 ∪ Ioi 3 := by 
  have h2 : (2 - x) / (x ^ 3 + x ^ 2) - (1 - 2 * x) / (x ^ 3 - 3 * x ^ 2) > 0 := by 
    linarith
  obtain ⟨neq1, neq2, neq3⟩ := hx
  have eq_aux : x ^ 2 + 6 * x - 7 = (x + 7) * (x -1) :=by 
    ring
  have neq4 : x ^ 3 + x ^ 2 ≠ 0 := by
    have aux : x ^ 3 + x ^ 2 = (x ^ 2) * (x + 1 ) := by 
      ring
    rw [aux]
    apply mul_ne_zero_iff.mpr
    constructor
    exact pow_ne_zero 2 neq1
    by_contra hc
    have xeq : x = -1 := by linarith
    exact neq2 xeq
  have neq5 : x ^ 3 - 3 * x ^ 2 ≠ 0 := by
    have aux : x ^ 3 - 3 * x ^ 2 = x ^ 2 * (x - 3) := by
      ring
    rw [aux]
    apply mul_ne_zero_iff.mpr
    constructor
    exact pow_ne_zero 2 neq1
    by_contra hc
    have xeq : x = 3 := by linarith
    exact neq3 xeq
  have h3 : (2 - x) / (x ^ 3 + x ^ 2) - (1 - 2 * x) / (x ^ 3 - 3 * x ^ 2) = 
    (x ^ 2 + 6 * x - 7) / ( x ^ 2 * (x + 1) * (x -3 )) := by 
    have aux : (x ^ 2 * ((x + 1) * (x - 3))) ≠ 0 := by 
      apply mul_ne_zero_iff.mpr
      constructor
      exact pow_ne_zero 2 neq1
      apply mul_ne_zero_iff.mpr
      constructor
      by_contra hc
      have : x = -1 := by linarith
      exact neq2 this
      by_contra hc
      have : x = 3 := by linarith
      exact neq3 this
    field_simp
    have aux' : (x ^ 2 * (x + 1) * (x - 3)) = (x ^ 2 * ((x + 1) * (x - 3)))  := by 
      ring
    rw [←aux'] at aux
    field_simp
    ring
  rw [h3] at h2
  have : ((x ^ 2 + 6 * x - 7) > 0 ∧  ( x ^ 2 * (x + 1) * (x - 3 )) > 0)
    ∨ ((x ^ 2 + 6 * x - 7) < 0 ∧  ( x ^ 2 * (x + 1) * (x - 3 )) < 0) := by
    exact div_pos_iff.mp h2
  obtain h4 | h4 := this
  obtain ⟨h5, h6⟩ := h4
  rw [eq_aux] at h5
  have xpos : x ^ 2 > 0 := by 
    positivity
  have xpos2 : (x + 1) * (x - 3) > 0 := by 
    by_contra hc
    simp at hc
    nlinarith
  have ineq4 : (x + 1 > 0 ∧ x - 3 > 0 ) ∨ (x + 1 < 0 ∧ x - 3 < 0) := by 
    exact pos_and_pos_or_neg_and_neg_of_mul_pos xpos2
  have ineq1 : (x + 7 > 0 ∧ x - 1> 0) ∨ (x + 7 < 0 ∧ x - 1 < 0) := by 
    exact pos_and_pos_or_neg_and_neg_of_mul_pos h5
  obtain ineq2 | ineq2 := ineq1
  -- Case : x + 7 > 0 ∧ x - 1 > 0
  obtain ⟨ineq2, ineq3⟩ := ineq2
  have xgt : x > 1 := by linarith
  have ineq4 : (x + 1 > 0 ∧ x - 3 > 0 ) ∨ (x + 1 < 0 ∧ x - 3 < 0) := by 
    exact pos_and_pos_or_neg_and_neg_of_mul_pos xpos2
  obtain ineq5 | ineq5 := ineq4
  obtain ⟨ineq5, ineq6⟩ := ineq5
  have xgt' : x > 3 := by linarith
  right
  simpa
  obtain ⟨ineq5, ineq6⟩ := ineq5
  have xlt : x < -1 := by linarith
  linarith
  obtain ineq5 | ineq5 := ineq4
  obtain ⟨ineq5, ineq6⟩ := ineq5
  obtain ⟨ineq2, ineq3⟩ := ineq2
  linarith
  obtain ⟨ineq5, ineq6⟩ := ineq5
  obtain ⟨ineq2, ineq3⟩ := ineq2
  have xlt : x < -7 := by linarith
  left; left;left
  simpa
  obtain ⟨ineq1, ineq2⟩ := h4
  have xpos : x ^ 2 > 0 := by 
    positivity
  have xpos2 : (x + 1) * (x - 3) < 0 := by 
    by_contra hc
    simp at hc
    nlinarith
  rw [eq_aux] at ineq1
  have ineq4 : (x + 1 > 0 ∧ x - 3 < 0 ) ∨ (x + 1 < 0 ∧ x - 3 > 0) := by
    exact mul_neg_iff.mp xpos2
  have ineq5 : (x + 7 > 0 ∧ x - 1< 0) ∨ (x + 7 < 0 ∧ x - 1 > 0) := by
    exact mul_neg_iff.mp ineq1
  obtain ineq6 | ineq6 := ineq5
  obtain ⟨ineq6, ineq7⟩ := ineq6
  obtain  ineq8 | ineq9 := ineq4
  by_cases hxpos : x > 0 
  have xlt : x < 1 := by 
    linarith
  left
  right
  simp
  constructor
  simp_all
  simp_all
  have xneg : x < 0 := by 
    nlinarith
  have xin : x > -1 := by linarith
  left; left; right
  simp
  constructor
  simpa; simpa
  obtain ⟨h4, h5⟩ := ineq9
  have xgt : x > 3 := by linarith
  right
  simpa
  obtain h4 | h4 := ineq4
  obtain ⟨h4, h5⟩ := h4
  obtain ⟨ineq6, ineq7⟩ := ineq6
  linarith
  obtain ⟨h4, h5⟩ := h4
  obtain ⟨ineq6, ineq7⟩ := ineq6
  have xlt : x < -7 := by linarith
  left; left; left
  simpa