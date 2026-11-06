import Mathlib

theorem algebra_112739 {x y z : ℝ} (h1 : x + y + z = 2) (h2 : x^2 + y^2 + z^2 = 6) (h3 : x^3 + y^3 + z^3 = 8) :
    (x = -1 ∧ y = 1 ∧ z = 2) ∨ (x = 1 ∧ y = -1 ∧ z = 2) ∨ (x = 1 ∧ y = 2 ∧ z = -1) ∨ (x = -1 ∧ y = 2 ∧ z = 1) ∨
    (x = 2 ∧ y = -1 ∧ z = 1) ∨ (x = 2 ∧ y = 1 ∧ z = -1) := by
  have h4 : x * y + y * z + z * x = -1 := by
    have eq1 : x ^ 2 + y ^ 2 + z ^ 2 = (x + y + z) ^ 2 - 2 * (x * y + y * z + z * x) := by
      ring
    rw [h1] at eq1
    linarith
  have h5 : x * y * z = -2 := by
    have eq1 : x ^ 3 + y ^ 3 + z ^ 3 - 3 * (x * y * z) = (x + y + z) * ((x ^ 2 + y ^ 2 + z ^ 2) - (x * y + y * z + z * x)) := by
      ring
    rw [h1, h2, h4] at eq1
    linarith [h3, eq1]

  have h6 : x = -1 ∨ x = 1 ∨ x = 2 := by
    have eq_x : (x - 1) * (x - 2) * (x + 1) = 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x + y + z - 2), sq_nonneg (x * y + y * z + z * x + 1), sq_nonneg (x * y * z + 2)]
    cases' (mul_eq_zero.mp eq_x) with h h
    cases' (mul_eq_zero.mp h) with h11 h12
    · -- x - 1 = 0
      right
      left
      linarith
    · -- x - 2 = 0
      right
      right
      linarith
    · -- x + 1 = 0
      left
      linarith

  rcases h6 with hx | hx | hx
  · -- Case x = -1
    have h8 : y + z = 3 := by
      nlinarith [h1, hx]
    have h9 : y * z = 2 := by
      have eq1 : x * y * z = -2 := h5
      rw [hx] at eq1
      nlinarith
    have h10 : (y - 1) * (y - 2) = 0 := by
      nlinarith [sq_nonneg (y - z), h8, h9]
    cases' (mul_eq_zero.mp h10) with hy1 hy2
    · -- y - 1 = 0, so y = 1, then z = 2
      have hy : y = 1 := by linarith
      have hz : z = 2 := by linarith [h8, hy]
      simp [hx, hy, hz]
      <;> tauto
    · -- y - 2 = 0, so y = 2, then z = 1
      have hy : y = 2 := by linarith
      have hz : z = 1 := by linarith [h8, hy]
      simp [hx, hy, hz]
      <;> tauto
  · -- Case x = 1
    have h8 : y + z = 1 := by
      nlinarith [h1, hx]
    have h9 : y * z = -2 := by
      have eq1 : x * y * z = -2 := h5
      rw [hx] at eq1
      nlinarith
    have h10 : (y - 2) * (y + 1) = 0 := by
      nlinarith [sq_nonneg (y - z), h8, h9]
    cases' (mul_eq_zero.mp h10) with hy1 hy2
    · -- y - 2 = 0, so y = 2, then z = -1
      have hy : y = 2 := by linarith
      have hz : z = -1 := by linarith [h8, hy]
      simp [hx, hy, hz]
      <;> tauto
    · -- y + 1 = 0, so y = -1, then z = 2
      have hy : y = -1 := by linarith
      have hz : z = 2 := by linarith [h8, hy]
      simp [hx, hy, hz]
      <;> tauto
  · -- Case x = 2
    have h8 : y + z = 0 := by
      nlinarith [h1, hx]
    have h9 : y * z = -1 := by
      have eq1 : x * y * z = -2 := h5
      rw [hx] at eq1
      nlinarith
    have h10 : z = -y := by linarith [h8]
    rw [h10] at h9
    have h11 : (y - 1) * (y + 1) = 0 := by
      have h12 : y ^ 2 = 1 := by linarith
      nlinarith [sq_nonneg y, h12]
    cases' (mul_eq_zero.1 h11) with hy1 hy2
    · -- Case y = 1
      have hy : y = 1 := by linarith
      have hz : z = -1 := by linarith [h10, hy]
      simp [hx, hy, hz]
      <;> tauto
    · -- Case y = -1
      have hy : y = -1 := by linarith
      have hz : z = 1 := by linarith [h10, hy]
      simp [hx, hy, hz]
      <;> tauto