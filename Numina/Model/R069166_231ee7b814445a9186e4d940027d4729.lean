import Mathlib

theorem algebra_167150 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hle : a ≤ b ∧ a ≤ c) (h : (a^2 + b^2 + c^2) / (a * (b + c)) = 3 / 2) :
    a = b ∧ b = c := by
  have h1 : 0 < a * (b + c) := by
    apply mul_pos
    exact ha
    linarith [hb, hc]
  
  have eq1 : a^2 + b^2 + c^2 = 3 / 2 * (a * (b + c)) := by 
    field_simp [h1] at h
    linarith
  
  have eq2 : 2 * (a^2 + b^2 + c^2) = 3 * a * (b + c) := by
    linarith [eq1]

  have h2 : a ≤ b := hle.1
  have h3 : a ≤ c := hle.2
  
  have h4 : b + c ≥ 2 * a := by 
    nlinarith
  
  have h5 : b^2 + c^2 ≥ 2 * a^2 := by 
    nlinarith [sq_nonneg (b - a), sq_nonneg (c - a), sq_nonneg (b + c - 2*a), h4]

  have eq3 : (b + c) = 2 * a := by 
    nlinarith [sq_nonneg (b - c), sq_nonneg (b + c - 2*a), h4, h5, eq2, mul_pos ha (show 0 < b + c by positivity)]
  
  have eq4 : b = a := by 
    nlinarith [h2, sq_nonneg (b - a), sq_nonneg (c - a), sq_nonneg (b + c - 2 * a)]

  have eq5 : c = a := by 
    nlinarith [h3, sq_nonneg (b - a), sq_nonneg (c - a), sq_nonneg (b + c - 2 * a)]

  constructor
  · linarith [eq4]
  · linarith [eq4, eq5]