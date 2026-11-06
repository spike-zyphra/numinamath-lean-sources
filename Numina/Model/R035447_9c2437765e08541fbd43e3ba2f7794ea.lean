import Mathlib

theorem algebra_103278 (u f d : ℝ) (x y z : ℝ)
    (huf : u / f = 1 / 2) (hfd : f / d = 2 / 3) (hufd : u + f +d = 50)
    (h₆ : x = 3) (h₇ : (u / x) / (f / y) = 4 / 5) (h₈ : (f / y) / (d / z) = 5 / 6) :
    u / x + f / y + d / z = 10 + 5 / 12 := by

  have hf1 : f ≠ 0 := by
    by_contra h
    have h1 : u / f = 0 := by
      rw [h]
      norm_num
    linarith

  have hd1 : d ≠ 0 := by
    by_contra h
    have h1 : f / d = 0 := by
      rw [h]
      norm_num
    linarith

  have h1 : 2 * u = f := by
    have h : f ≠ 0 := hf1
    field_simp at huf
    linarith

  have h2 : 3 * f = 2 * d := by
    have h : d ≠ 0 := hd1
    field_simp at hfd
    linarith

  have h3 : f = 2 * u := by linarith

  have h4 : d = 3 * u := by
    rw [h3] at h2
    linarith

  have h5 : u = 25 / 3 := by
    have h6 : u + f + d = 50 := hufd
    rw [show f = 2 * u by linarith [h3]] at h6
    rw [show d = 3 * u by linarith [h4]] at h6
    linarith

  have h6' : f = 50 / 3 := by
    linarith [h3, h5]

  have h8' : d = 25 := by
    linarith [h4, h5]

  have h7' : x = 3 := h₆

  have h9 : y = 24 / 5 := by
    rw [h7'] at h₇
    have eq1 : u = 25 / 3 := h5
    have eq2 : f = 50 / 3 := h6'
    rw [eq1, eq2] at h₇
    have eq3 : (25 / 3 : ℝ) / (3 : ℝ) / ((50 / 3 : ℝ) / y) = 4 / 5 := by
      linarith
    field_simp [(show y ≠ 0 by
      by_contra h
      rw [h] at eq3
      norm_num at eq3
    )] at eq3 ⊢
    linarith

  have h10 : z = 6 := by
    have eq1 : f / y = (50 / 3 : ℝ) / (24 / 5) := by
      rw [show f = 50 / 3 by linarith [h6']]
      rw [show y = 24 / 5 by linarith [h9]]
    have eq2 : (f / y) / (d / z) = 5 / 6 := h₈
    have eq3 : d = (25 : ℝ) := by
      linarith [h8']
    rw [eq1, eq3] at eq2
    have eq4 : ((50 / 3 : ℝ) / (24 / 5)) / ((25 : ℝ) / z) = 5 / 6 := by
      linarith
    field_simp [(show z ≠ 0 by
      by_contra h
      rw [h] at eq4
      norm_num at eq4
    )] at eq4 ⊢
    nlinarith

  rw [h₆, h9, h10]
  rw [show u = 25 / 3 by linarith [h5]]
  rw [show f = 50 / 3 by linarith [h6']]
  rw [show d = (25 : ℝ) by linarith [h8']]
  norm_num