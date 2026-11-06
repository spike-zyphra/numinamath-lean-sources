import Mathlib

theorem algebra_96906 {xA yA xB yB : ℝ} (hA : 4 * xA^2 + 7 * xA - 1 = yA) (hB : 4 * xB^2 + 7 * xB - 1 = yB)
(hxAB : (xA + xB) / 2 = 0) (hyAB : (yA + yB) / 2 = 0) : Real.sqrt ((xB - xA)^2 + (yB - yA)^2) = 5 * Real.sqrt 2 := by
  have h1 : xA + xB = 0 := by
    linarith
  have h2 : xB = -xA := by
    linarith
  have h3 : yA + yB = 0 := by
    linarith
  have h4 : yB = -yA := by
    linarith
  rw [h2] at hB
  rw [h4] at hB
  have eq3 : xA^2 = 1 / 4 := by
    nlinarith [hA, hB]
  have eq4 : xA = 1 / 2 ∨ xA = -1 / 2 := by
    have h5 : xA ^ 2 - (1 / 4) = 0 := by
      linarith
    have h6 : (xA - 1 / 2) * (xA + 1 / 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h6) with h7 h8
    · -- case xA - 1/2 = 0
      left
      linarith
    · -- case xA + 1/2 = 0
      right
      linarith
  rcases eq4 with h5 | h5
  · -- Case xA = 1/2, so xB = -1/2
    have hx1 : xA = 1 / 2 := h5
    have hx2 : xB = -1 / 2 := by
      rw [show xA = 1 / 2 by linarith [hx1]] at h2
      linarith
    have hy1 : yA = 7 / 2 := by
      rw [hx1] at hA
      nlinarith
    have hy2 : yB = -7 / 2 := by
      linarith [hy1, h4]
    have h7 : (xB - xA)^2 + (yB - yA)^2 = 50 := by
      rw [hx1, hx2, hy1, hy2]
      norm_num
    rw [h7]
    have h8 : Real.sqrt (50 : ℝ) = 5 * Real.sqrt 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h8]
  · -- Case xA = -1/2, so xB = 1/2
    have hx1 : xA = -1 / 2 := h5
    have hx2 : xB = 1 / 2 := by
      rw [show xA = -1 / 2 by linarith [hx1]] at h2
      linarith
    have hy1 : yA = -7 / 2 := by
      rw [hx1] at hA
      nlinarith
    have hy2 : yB = 7 / 2 := by
      linarith [hy1, h4]
    have h7 : (xB - xA)^2 + (yB - yA)^2 = 50 := by
      rw [hx1, hx2, hy1, hy2]
      norm_num
    rw [h7]
    have h8 : Real.sqrt (50 : ℝ) = 5 * Real.sqrt 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h8]