import Mathlib


theorem algebra_599067 (x y z : ℝ) (hd : x + y + z ≠ 0) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) (hz : 0 ≤ z ∧ z ≤ 1)
    (h : x / (1 + y + z * x) + y / (1 + z + x * y) + z / (1 + x + y * z) = 3 / (x + y + z)) :
    x = 1 ∧ y = 1 ∧ z = 1 := by
  have hx0 : 0 ≤ x := hx.1
  have hx1 : x ≤ 1 := hx.2
  have hy0 : 0 ≤ y := hy.1
  have hy1 : y ≤ 1 := hy.2
  have hz0 : 0 ≤ z := hz.1
  have hz1 : z ≤ 1 := hz.2
  have h1 : 0 < x + y + z := by
    by_contra h2
    push_neg at h2
    have : x + y + z = 0 := by linarith
    contradiction

  have h2 : x / (1 + y + z * x) ≤ x / (x + y + z) := by
    have hx0' : 0 ≤ x := hx0
    have hx1' : 0 < 1 + y + z * x := by nlinarith
    have hx2' : 0 < x + y + z := by linarith
    have h3 : 1 + y + z * x ≥ x + y + z := by
      nlinarith [show (0 : ℝ) ≤ (1 - x) * (1 - z) by nlinarith]
    have h4 : x / (1 + y + z * x) ≤ x / (x + y + z) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    linarith

  have h3 : y / (1 + z + x * y) ≤ y / (x + y + z) := by
    have hy0' : 0 ≤ y := hy0
    have hy1' : 0 < 1 + z + x * y := by nlinarith
    have hy2' : 0 < x + y + z := by linarith
    have h4 : 1 + z + x * y ≥ x + y + z := by
      nlinarith [show (0 : ℝ) ≤ (1 - y) * (1 - x) by nlinarith]
    have h5 : y / (1 + z + x * y) ≤ y / (x + y + z) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    linarith

  have h4 : z / (1 + x + y * z) ≤ z / (x + y + z) := by
    have hz0' : 0 ≤ z := hz0
    have hz1' : 0 < 1 + x + y * z := by nlinarith
    have hz2' : 0 < x + y + z := by linarith
    have h5 : 1 + x + y * z ≥ x + y + z := by
      nlinarith [show (0 : ℝ) ≤ (1 - z) * (1 - y) by nlinarith]
    have h6 : z / (1 + x + y * z) ≤ z / (x + y + z) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    linarith

  have h5 : x / (1 + y + z * x) + y / (1 + z + x * y) + z / (1 + x + y * z) ≤ 1 := by
    have h6 : x / (1 + y + z * x) + y / (1 + z + x * y) + z / (1 + x + y * z) ≤ x / (x + y + z) + y / (x + y + z) + z / (x + y + z) := by
      linarith [h2, h3, h4]
    have h7 : x / (x + y + z) + y / (x + y + z) + z / (x + y + z) = (x + y + z) / (x + y + z) := by
      ring
    have h8 : (x + y + z) / (x + y + z) = 1 := by
      field_simp [(show x + y + z ≠ 0 by assumption)]
    linarith [h6, h7, h8]

  have h6 : 3 / (x + y + z) ≤ 1 := by
    linarith [h, h5]

  have h7 : 3 ≤ x + y + z := by
    have h8 : 0 < x + y + z := h1
    have h9 : 3 / (x + y + z) ≤ 1 := h6
    have h10 : 3 ≤ x + y + z := by
      by_contra h
      push_neg at h
      have h11 : x + y + z < (3 : ℝ) := by linarith
      have h12 : 3 / (x + y + z) > 1 := by
        apply (lt_div_iff' (by linarith)).mpr
        nlinarith
      linarith
    linarith

  have h8 : x + y + z = 3 := by
    nlinarith [show x + y + z ≤ 3 by nlinarith]

  have hx2 : x = 1 := by
    nlinarith [show y + z ≤ 2 by nlinarith]

  have hy2 : y = 1 := by
    nlinarith [show x + z ≤ 2 by nlinarith]

  have hz2 : z = 1 := by
    nlinarith [show x + y ≤ 2 by nlinarith]

  exact ⟨hx2, hy2, hz2⟩