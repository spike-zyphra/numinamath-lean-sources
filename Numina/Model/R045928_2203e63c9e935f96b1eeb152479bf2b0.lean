import Mathlib

theorem algebra_230490 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h : (x * 1.4) / (y * (1 - z)) = 2 * (x / y)) :
    z = 0.3 := by

  have h1 : y * (1 - z) ≠ 0 := by
    apply mul_ne_zero
    · linarith
    · by_contra h2
      have h3 : 1 - z = 0 := by
        nlinarith
      have h4 : z = 1 := by linarith
      rw [h4] at h
      field_simp [hy, h4] at h
      all_goals nlinarith

  have eq1 : x * 1.4 = 2 * x * (1 - z) := by
    have eq2 : (x * 1.4) / (y * (1 - z)) = 2 * (x / y) := h
    have eq3 : (x * 1.4) = (2 * (x / y)) * (y * (1 - z)) := by
      have h2 : (y * (1 - z)) ≠ 0 := h1
      field_simp [h2] at eq2 ⊢
      nlinarith
    have eq4 : (2 * (x / y)) * (y * (1 - z)) = 2 * x * (1 - z) := by
      field_simp [hy] at *
      <;> ring
      <;> field_simp [hy]
      <;> ring
    rw [eq4] at eq3
    linarith

  have h2 : (1.4 : ℝ) = 2 * (1 - z) := by
    apply (mul_left_inj' (show x ≠ 0 by linarith)).mp
    nlinarith

  have h3 : z = (0.3 : ℝ) := by
    ring_nf at h2 ⊢
    nlinarith

  linarith