import Mathlib

theorem algebra_223387 {x y z : ℝ} (h1 : x^2 - y = z^2) (h2 : y^2 - z = x^2) (h3 : z^2 - x = y^2) :
    (x, y, z) = (0, 0, 0) ∨ (x, y, z) = (1, 0, -1) ∨ (x, y, z) = (0, -1, 1) ∨ (x, y, z) = (-1, 1, 0) := by

  have h4 : x + y + z = 0 := by
    nlinarith

  have h5 : z = -x - y := by
    linarith

  rw [h5] at h1
  have h6 : y * (y + 2 * x + 1) = 0 := by
    nlinarith

  cases' (mul_eq_zero.1 h6) with hy1 hy2

  · -- Case y = 0
    have hy : y = 0 := by linarith

    have h7 : z = -x := by
      linarith [h4, hy]

    have h8 : x * (x - 1) = 0 := by
      rw [hy, h7] at h2
      nlinarith

    cases' (mul_eq_zero.1 h8) with hx1 hx2

    · -- Case x = 0
      have hx : x = 0 := by linarith

      have h9 : z = 0 := by
        linarith [hx, h7]

      left
      simp [hx, hy, h9]

    · -- Case x - 1 = 0, so x = 1
      have hx : x = 1 := by linarith

      have h10 : z = -1 := by
        linarith [hx, h7]

      right
      left
      simp [hx, hy, h10]

  · -- Case y + 2 * x + 1 = 0
    have hy : y = -2 * x - 1 := by linarith

    have h7 : z = x + 1 := by
      rw [hy] at h5
      linarith

    have h8 : x * (x + 1) = 0 := by
      rw [hy, h7] at h2
      nlinarith

    cases' (mul_eq_zero.1 h8) with hx1 hx2

    · -- Case x = 0
      have hx : x = 0 := by linarith

      have h9 : y = -1 := by
        linarith [hx, hy]

      have h10 : z = 1 := by
        linarith [hx, h7]

      right
      right
      left
      simp [hx, h9, h10]

    · -- Case x + 1 = 0, so x = -1
      have hx : x = -1 := by linarith

      have h9 : y = 1 := by
        linarith [hx, hy]

      have h10 : z = 0 := by
        linarith [hx, h7]

      right
      right
      right
      simp [hx, h9, h10]