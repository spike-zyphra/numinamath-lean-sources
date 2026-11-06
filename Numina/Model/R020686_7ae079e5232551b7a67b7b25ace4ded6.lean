import Mathlib

theorem algebra_193655 {x : ℝ} (hx : x > 0) (h : (60 - 10) / (x - 5) = 60 / x + 1) :
    x = 15 := by
  have h1 : x - 5 ≠ 0 := by
    by_contra h1
    have : x = 5 := by linarith
    rw [this] at h
    norm_num at h
    all_goals linarith
  have h2 : x ≠ 0 := by
    by_contra h2
    rw [h2] at h
    norm_num at h
    all_goals linarith
  have eq1 : (60 - 10 : ℝ) / (x - 5) = 60 / x + 1 := h
  have h4 : x - 5 ≠ 0 := h1
  have h5 : x ≠ 0 := h2
  have eq2 : (60 - 10 : ℝ) / (x - 5) * (x) * (x - 5) = 50 * x := by
    have h3 : x - 5 ≠ 0 := h4
    have eq3 : (60 - 10 : ℝ) / (x - 5) * (x) * (x - 5) = ((60 - 10 : ℝ) / (x - 5) * (x - 5)) * x := by ring
    rw [eq3]
    have eq4 : (60 - 10 : ℝ) / (x - 5) * (x - 5) = (60 - 10 : ℝ) := by
      field_simp [h3]
      all_goals nlinarith
    rw [eq4]
    all_goals ring_nf
    all_goals nlinarith
  have eq3 : (60 / x + 1) * (x) * (x - 5) = 60 * (x - 5) + x * (x - 5) := by
    have h4 : x ≠ 0 := h5
    field_simp [h4]
    <;> ring_nf
    <;> nlinarith
    all_goals ring
  have eq4 : (60 - 10 : ℝ) * (x) = 60 * (x - 5) + x * (x - 5) := by
    have eq5 : (60 - 10 : ℝ) / (x - 5) * (x) * (x - 5) = (60 / x + 1) * (x) * (x - 5) := by
      rw [eq1]
    have eq6 : (60 - 10 : ℝ) / (x - 5) * (x) * (x - 5) = 50 * x := eq2
    have eq7 : (60 / x + 1) * (x) * (x - 5) = 60 * (x - 5) + x * (x - 5) := eq3
    nlinarith [eq5, eq6, eq7]
  have h3 : x^2 + 5 * x - 300 = 0 := by
    nlinarith [eq4]
  have h4 : (x - 15) * (x + 20) = 0 := by
    nlinarith [h3]
  cases' (mul_eq_zero.1 h4) with h5 h6
  · -- Case x - 15 = 0, so x = 15
    linarith
  · -- Case x + 20 = 0, so x = -20
    nlinarith