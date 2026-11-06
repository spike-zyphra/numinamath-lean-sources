import Mathlib

theorem algebra_266363 (p1 p2 : ℝ) (hp1 : p1 ∈ Set.Icc 0 1) (hp2 : p2 ∈ Set.Icc 0 1)
    (h1 : (1 - p1) * (1 - p2) = p1 * p2) (h2 : p1 * p2 = p1 * (1 - p2) + p2 * (1 - p1)) :
    False := by
  have hp11 : 0 ≤ p1 := hp1.1
  have hp12 : p1 ≤ 1 := hp1.2
  have hp21 : 0 ≤ p2 := hp2.1
  have hp22 : p2 ≤ 1 := hp2.2
  
  have h3 : p1 + p2 = 1 := by 
    nlinarith
  
  have h4 : p1 * p2 = 1 / 3 := by
    have h5 : p1 + p2 = 1 := h3
    nlinarith
  
  have h6 : (p1 - p2) ^ 2 ≥ 0 := by
    apply sq_nonneg
  
  nlinarith [sq_nonneg (p1 - p2)]