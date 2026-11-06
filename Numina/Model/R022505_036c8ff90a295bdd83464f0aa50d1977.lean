import Mathlib

theorem algebra_100569 (a b : ℤ) (ha : a ≠ 0) (h : ∀ x : ℤ, x^2 + a * x + b < 0 ↔ x^2 + x - 110 < 0 ∧ x^2 + 10 * x - 96 < 0) :
    ⌊|a - b|⌋ ≤ 71 := by 
  have h1 := h (-11)
  norm_num at h1
  have h2 := h 6
  norm_num at h2
  have h3 := h (-10)
  norm_num at h3
  have h4 := h 5
  norm_num at h4
  have h5 := h (-12)
  norm_num at h5
  have h6 := h 7
  norm_num at h6
  have h7 := h (-9)
  norm_num at h7
  have h8 := h 0
  norm_num at h8
  have h9 := h 1
  norm_num at h9
  have h10 := h 2
  norm_num at h10
  have h11 := h 3
  norm_num at h11
  have h12 := h 4
  norm_num at h12
  have h13 := h (-1)
  norm_num at h13
  have h14 := h (-2)
  norm_num at h14
  have h15 : a ≤ 20 := by 
    omega
  have h16 : a ≥ -10 := by 
    omega
  interval_cases a <;> try { 
    omega 
  } <;> try { 
    have : b ≤ 100 := by 
      omega 
    have : b ≥ -100 := by 
      omega 
    interval_cases b <;> norm_num at *
    <;> omega 
  }