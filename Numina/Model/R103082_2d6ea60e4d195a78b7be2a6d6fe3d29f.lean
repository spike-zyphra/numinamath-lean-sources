import Mathlib

theorem algebra_4252 (v s : ℝ) (h : 0 < v) (h1 : 0 < s) (h2 : s / (v + 3) = 4) (h3 : s / (v - 3) = 4 + 40 / 60) :
    v = 39 := by
  have h4 : v + 3 > 0 := by nlinarith
  have h5 : v - 3 ≠ 0 := by
    by_contra h6
    have h7 : v = 3 := by linarith
    rw [h7] at h3
    norm_num at h3
    <;> linarith
  have eq1 : s = 4 * (v + 3) := by
    have h_eq1 : s / (v + 3) = 4 := h2
    field_simp [show v + 3 ≠ 0 by linarith] at h_eq1 ⊢
    linarith
  have eq2 : s = (14 / 3) * (v - 3) := by
    have h_eq1 : s / (v - 3) = 4 + 40 / 60 := h3
    field_simp [show v - 3 ≠ 0 by
      intro h5'
      apply h5
      linarith
    ] at h_eq1 ⊢
    nlinarith
  nlinarith [eq1, eq2]