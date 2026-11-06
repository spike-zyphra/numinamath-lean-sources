import Mathlib

theorem algebra_310217 (x y z : ℝ) (h1 : x + y + z = 6) (h2 : x^2 + y^2 + z^2 = 14)
    (h3 : x^3 + y^3 + z^3 = 36) :
    (x = 1 ∧ y = 2 ∧ z = 3) ∨ (x = 1 ∧ y = 3 ∧ z = 2) ∨
    (x = 2 ∧ y = 1 ∧ z = 3) ∨ (x = 2 ∧ y = 3 ∧ z = 1) ∨
    (x = 3 ∧ y = 1 ∧ z = 2) ∨ (x = 3 ∧ y = 2 ∧ z = 1) := by

  have h4 : x * y + y * z + z * x = 11 := by 
    have h5 : (x + y + z) ^ 2 = 36 := by
      nlinarith 
    nlinarith

  have h5 : x * y * z = 6 := by
    have eq1 : x^3 + y^3 + z^3 - 3 * (x * y * z) = 
        (x + y + z) * (x^2 + y^2 + z^2 - (x * y + y * z + z * x)) := by 
      ring
    rw [h1, h2, h4, h3] at eq1 
    linarith

  have h6 : (x - 1) * (x - 2) * (x - 3) = 0 := by
    have hx : x^3 - 6 * x^2 + 11 * x - 6 = 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y)]
    nlinarith

  cases' (mul_eq_zero.mp h6) with h7 h8
  cases' (mul_eq_zero.mp h7) with h8 h9
  · -- Case x - 1 = 0, so x = 1
    have hx1 : x = 1 := by linarith
    have h10 : y + z = 5 := by linarith 
    have h11 : y * z = 6 := by 
      have hx1' : x = 1 := hx1 
      have h5' : x * y * z = 6 := h5 
      rw [hx1'] at h5' 
      nlinarith 
    have h12 : (y - 2) * (y - 3) = 0 := by 
      nlinarith [sq_nonneg (y - 2), sq_nonneg (y - 3)]
    cases' (mul_eq_zero.mp h12) with h13 h14
    · -- Case y - 2 = 0, so y = 2 
      have hy2 : y = 2 := by linarith 
      have hz3 : z = 3 := by linarith 
      simp [hx1, hy2, hz3]
    · -- Case y - 3 = 0, so y = 3 
      have hy3 : y = 3 := by linarith 
      have hz2 : z = 2 := by linarith 
      simp [hx1, hy3, hz2]
  · -- Case x - 2 = 0, so x = 2 
    have hx2 : x = 2 := by linarith 
    have h10 : y + z = 4 := by linarith 
    have h11 : y * z = 3 := by 
      have hx2' : x = 2 := hx2 
      have h5' : x * y * z = 6 := h5 
      rw [hx2'] at h5' 
      nlinarith 
    have h12 : (y - 1) * (y - 3) = 0 := by 
      nlinarith [sq_nonneg (y - 1), sq_nonneg (y - 3)]
    cases' (mul_eq_zero.mp h12) with h13 h14 
    · -- Case y - 1 = 0, so y = 1 
      have hy1 : y = 1 := by linarith 
      have hz3 : z = 3 := by linarith 
      simp [hx2, hy1, hz3]
    · -- Case y - 3 = 0, so y = 3 
      have hy3 : y = 3 := by linarith 
      have hz1 : z = 1 := by linarith 
      simp [hx2, hy3, hz1]
  · -- Case x - 3 = 0, so x = 3 
    have hx3 : x = 3 := by linarith 
    have h10 : y + z = 3 := by linarith 
    have h11 : y * z = 2 := by 
      have hx3' : x = 3 := hx3 
      have h5' : x * y * z = 6 := h5 
      rw [hx3'] at h5' 
      nlinarith 
    have h12 : (y - 1) * (y - 2) = 0 := by 
      nlinarith [sq_nonneg (y - 1), sq_nonneg (y - 2)]
    cases' (mul_eq_zero.mp h12) with h13 h14 
    · -- Case y - 1 = 0, so y = 1 
      have hy1 : y = 1 := by linarith 
      have hz2 : z = 2 := by linarith 
      simp [hx3, hy1, hz2]
    · -- Case y - 2 = 0, so y = 2 
      have hy2 : y = 2 := by linarith 
      have hz1 : z = 1 := by linarith 
      simp [hx3, hy2, hz1]