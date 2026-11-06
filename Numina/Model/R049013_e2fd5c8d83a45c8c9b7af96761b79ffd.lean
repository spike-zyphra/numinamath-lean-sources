import Mathlib

theorem algebra_228929 {x y : ℝ} (hx : x + y ≥ 0) (hy : x - y ≥ 0)
    (h1 : x + y + Real.sqrt (x + y) = 6) (h2 : x - y + Real.sqrt (x - y) = 2) :
    x = 2.5 ∧ y = 1.5 := by
  let s := Real.sqrt (x + y)
  have hs2 : s ^ 2 = x + y := by
    rw [Real.sq_sqrt]
    linarith
  let t := Real.sqrt (x - y)
  have ht2 : t ^ 2 = x - y := by
    rw [Real.sq_sqrt]
    linarith
  have eq1 : s^2 + s = 6 := by
    have h1' : x + y + s = 6 := by
      linarith [h1]
    have h3 : x + y = s^2 := by
      linarith [hs2]
    nlinarith
  have eq2 : t^2 + t = 2 := by
    have h2' : x - y + t = 2 := by
      linarith [h2]
    have h4 : x - y = t^2 := by
      linarith [ht2]
    nlinarith
  have h3 : s = 2 := by
    nlinarith [Real.sqrt_nonneg (x + y), sq_nonneg (s - 2), sq_nonneg (s + 3)]
  have h4 : t = 1 := by
    nlinarith [Real.sqrt_nonneg (x - y), sq_nonneg (t - 1), sq_nonneg (t + 2)]
  have h5 : x + y = 4 := by
    have h3 : s = 2 := h3
    have hs2 : s ^ 2 = x + y := hs2
    rw [h3] at hs2
    nlinarith
  have h6 : x - y = 1 := by
    have h4 : t = 1 := h4
    have ht2 : t ^ 2 = x - y := ht2
    rw [h4] at ht2
    nlinarith
  have hx2 : x = 2.5 := by
    have eq1 : x + y = 4 := h5
    have eq2 : x - y = 1 := h6
    have eq3 : x + y + (x - y) = 4 + 1 := by linarith
    have eq4 : 2 * x = 5 := by linarith [eq3]
    have hx2 : x = 5 / 2 := by linarith
    rw [hx2]
    norm_num
  have hy2 : y = 1.5 := by
    have eq1 : x + y = 4 := h5
    have hx2 : x = 2.5 := hx2
    have eq2 : (2.5 : ℝ) + y = 4 := by linarith [eq1, hx2]
    have hy2 : y = 1.5 := by linarith
    exact hy2
  constructor
  · exact hx2
  · exact hy2