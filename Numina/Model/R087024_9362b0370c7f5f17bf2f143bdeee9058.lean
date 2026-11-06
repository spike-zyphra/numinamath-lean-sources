import Mathlib

theorem algebra_109864 {a : ℝ} (ha : ∃ x y, x ≠ y ∧ x^2 - 4 * a * x + 5 * a^2 - 6 * a = 0 ∧
    y^2 - 4 * a * y + 5 * a^2 - 6 * a = 0 ∧ |x - y| = 6) : a = 3 := by

  rcases ha with ⟨x, y, hxy, hx, hy, habs⟩

  have h_diff : (x - y) * (x + y - 4 * a) = 0 := by
    nlinarith

  cases' (mul_eq_zero.mp h_diff) with h1 h2

  · -- Case where x - y = 0, which contradicts x ≠ y
    exfalso
    exact hxy (by linarith)

  · -- Case where x + y - 4*a = 0, so x + y = 4*a
    have h3 : x + y = 4 * a := by linarith

    have h4 : (x - y) ^ 2 = 36 := by
      cases abs_cases (x - y) with
      | inl h => -- If |x - y| = x - y, then (x - y)^2 = 36
        nlinarith
      | inr h => -- If |x - y| = -(x - y), then (x - y)^2 = 36
        nlinarith

    have h5 : x * y = 5 * a ^ 2 - 6 * a := by
      nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hxy), hx, hy]

    have h6 : (x - y) ^ 2 = (x + y) ^ 2 - 4 * (x * y) := by
      ring

    rw [h3, h5] at h6
    nlinarith [h6, h4]