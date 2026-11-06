import Mathlib

theorem algebra_253106 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) 
    (h₁ : a + b > c) (h₂ : a + c > b) (h₃ : b + c > a)
    (h : 1 / (a + c) + 1 / (b + c) = 3 / (a + b + c)) :
    Real.arccos ((a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b)) = Real.pi / 3 := by
  have pos1 : 0 < a + b + c := by linarith
  have pos2 : 0 < a + c := by linarith
  have pos3 : 0 < b + c := by linarith
  field_simp at h
  ring_nf at h
  have h1 : a ^ 2 + b ^ 2 - c ^ 2 = a * b := by nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  have h2 : (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) = 1 / 2 := by
    rw [h1]
    field_simp
    nlinarith
  rw [h2]
  have h3 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
  have h4 : 0 ≤ Real.pi / 3 := by
    have pi_nonneg : 0 ≤ Real.pi := Real.pi_nonneg
    linarith
  have h5 : Real.pi / 3 ≤ Real.pi := by
    have pi_pos : 0 < Real.pi := Real.pi_pos
    linarith
  rw [←h3]
  apply Real.arccos_cos h4 h5