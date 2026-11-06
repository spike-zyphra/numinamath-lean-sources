import Mathlib

theorem algebra_257735 (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    (c : ℝ) (hc : 0 < c) (h : (a + 1) / (b + c) = b / a) : 1 ≤ c := by

  have h1 : (a : ℝ) > 0 := by exact_mod_cast (show a > 0 by linarith)
  have h2 : (b : ℝ) > 0 := by exact_mod_cast (show b > 0 by linarith)
  have h3 : (b + c) ≠ 0 := by
    have h4 : (b : ℝ) > 0 := h2
    have h5 : c > 0 := hc
    nlinarith

  have h4 : (a : ℝ) ≠ 0 := by
    exact_mod_cast show a ≠ 0 by linarith

  have h5 : (b + c : ℝ) ≠ 0 := by
    have h4 : (b : ℝ) > 0 := h2
    nlinarith

  have eq1 : (a + 1 : ℝ) / (b + c) = (b : ℝ) / (a : ℝ) := by
    simpa using h

  have eq2 : (a + 1 : ℝ) * (a : ℝ) = (b : ℝ) * (b + c) := by
    have h6 : (a : ℝ) ≠ 0 := h4
    have h7 : (b + c : ℝ) ≠ 0 := h3
    field_simp [h6, h7] at eq1 ⊢
    nlinarith [eq1]

  have eq4 : a ≥ b := by
    by_contra h8
    push_neg at h8
    have h13 : a < b := h8
    have h14 : a < b := h13
    have h15 : a * (a + 1) < (b * b : ℤ) := by
      have h16 : a < b := h14
      nlinarith [sq_nonneg (a - b : ℤ)]

    have eq7 : (a : ℝ) * (a + 1 : ℝ) = (b : ℝ) * (b + c) := by 
      nlinarith [eq2]
    
    have eq8 : (a * (a + 1) : ℝ) < (b * b : ℝ) := by
      exact_mod_cast (show a * (a + 1) < b * b by linarith [h15])

    nlinarith

  have eq5 : c ≥ 1 := by
    have eq2' : (a : ℝ) * (a + 1 : ℝ) = (b : ℝ) * (b + c) := by
      nlinarith [eq2]

    have h11 : (a : ℝ) ≥ (b : ℝ) := by
      exact_mod_cast eq4

    nlinarith [sq_nonneg ( (a : ℝ) - (b : ℝ) ), sq_nonneg (c - 1 : ℝ), mul_pos h1 h2 ]

  linarith