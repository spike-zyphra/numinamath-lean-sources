import Mathlib

theorem algebra_182363 {x y : ℝ} (hy : y ≠ 0) (h : (x * 0.92) / (y * 1.08) = x / y - 2) :
    x / y = 27 / 2 := by
  have eq1 : x * 0.92 = (x / y - 2) * (y * 1.08) := by
    have eq2 : (y * 1.08) ≠ 0 := by
      by_contra h1
      have : y = 0 := by
        norm_num at h1 ⊢
        linarith
      contradiction
    field_simp [hy] at h ⊢
    nlinarith
  have eq2 : x * 0.92 = x * 1.08 - 2.16 * y := by
    have eq3 : (x / y - 2) * (y * 1.08) = x * 1.08 - 2.16 * y := by
      field_simp [hy]
      <;> ring_nf
    rw [eq3] at eq1
    all_goals linarith
  have eq3 : x * (0.92 : ℝ) - x * (1.08 : ℝ) = -2.16 * y := by
    linarith [eq2]
  have eq4 : x * (-0.16 : ℝ) = -2.16 * y := by
    ring_nf at eq3 ⊢
    linarith [eq3]
  have eq5 : x * (0.16 : ℝ) = 2.16 * y := by
    have eq6 : x * (-0.16 : ℝ) = -2.16 * y := eq4
    have eq7 : x * (0.16 : ℝ) = 2.16 * y := by
      calc
        x * (0.16 : ℝ) = - (x * (-0.16 : ℝ)) := by ring_nf
        _ = - (-2.16 * y) := by rw [eq6]
        _ = 2.16 * y := by ring_nf
    linarith [eq7]
  have eq6 : x / y = (2.16 / 0.16 : ℝ) := by
    have eq8 : x * (0.16 : ℝ) = 2.16 * y := eq5
    have eq9 : y ≠ 0 := hy
    have eq10 : x / y = (2.16 / 0.16 : ℝ) := by
      field_simp [eq9] at *
      nlinarith
    exact_mod_cast eq10
  rw [eq6]
  norm_num