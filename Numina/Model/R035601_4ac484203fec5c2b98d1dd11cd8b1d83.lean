import Mathlib

theorem algebra_263397 {a b : ℝ} (ha : a > b) (hb : b > 2)
    (h : ∃ x y z w, x^2 = y * z ∧ y^2 = z * w ∧ z^2 = w * x ∧
      (a + b) = x ∧ (a - b) = y ∧ (a * b) = z ∧ (b / a) = w) :
    a = 7 + 5 * √2 := by
  rcases h with ⟨x, y, z, w, h1, h2, h3, h4, h5, h6, h7⟩
  have h8 : a > b := ha
  have h9 : b > 2 := hb
  have h10 : x = a + b := by linarith
  have h11 : y = a - b := by linarith
  have h12 : z = a * b := by linarith
  have h13 : w = b / a := by
    linarith
  -- Substitute expressions for x, y, z, w into the equations
  rw [h10] at h1
  rw [h11] at h1
  rw [h12] at h1
  rw [h11] at h2
  rw [h12] at h2
  rw [h13] at h2
  rw [h12] at h3
  rw [h13] at h3
  rw [h10] at h3
  have h14 : a ≠ 0 := by nlinarith
  field_simp at h1 h2 h3 h7
  nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_pos_of_pos (show (a - b) > 0 by nlinarith), sq_pos_of_pos (show (b - 2) > 0 by nlinarith), Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num)]