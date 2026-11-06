import Mathlib

theorem algebra_194717 {x : ℝ} (hx : x ≠ 1 ∧ x ≠ 2 ∧ x ≠ 3 ∧ x ≠ 4) (h : x / ((x - 1) * (x - 4)) = x / ((x - 2) * (x - 3))) : x = 0 := by
  have h1 : x ≠ 1 := hx.1
  have h2 : x ≠ 2 := hx.2.1
  have h3 : x ≠ 3 := hx.2.2.1
  have h4 : x ≠ 4 := hx.2.2.2
  have h5 : x - 1 ≠ 0 := by
    intro h6
    apply h1
    linarith 
  have h6 : x - 2 ≠ 0 := by
    intro h7
    apply h2
    linarith 
  have h7 : x - 3 ≠ 0 := by
    intro h8
    apply h3
    linarith 
  have h8 : x - 4 ≠ 0 := by
    intro h9
    apply h4
    linarith
  have eq1 : ((x - 1) * (x - 4)) ≠ 0 := by 
    apply mul_ne_zero 
    exact h5
    exact h8
  have eq2 : ((x - 2) * (x - 3)) ≠ 0 := by
    apply mul_ne_zero
    exact h6
    exact h7
  
  by_cases h9 : x = 0
  · exact h9
  · have h10 : x ≠ 0 := by
      intro h11
      apply h9
      linarith
    have h11 : ((x - 2) * (x - 3)) = ((x - 1) * (x - 4)) := by
      have h12 : x / ((x - 1) * (x - 4)) = x / ((x - 2) * (x - 3)) := h
      field_simp [h5, h6, h7, h8, h10] at h12 ⊢
      nlinarith
    exfalso
    have h13 : ((x - 2) * (x - 3)) - ((x - 1) * (x - 4)) = 0 := by
      nlinarith [h11]
    exfalso
    have h14 : 2 = 0 := by
      nlinarith [h13]
    linarith