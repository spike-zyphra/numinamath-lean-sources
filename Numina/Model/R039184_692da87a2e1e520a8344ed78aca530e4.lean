import Mathlib

theorem algebra_123750 {a b c x y z : ℝ} (h : x^2 - y^2 - z^2 = 2*a*y*z) (h' : -x^2 + y^2 - z^2 = 2*b*z*x) (h'' : -x^2 - y^2 + z^2 = 2*c*x*y) (h''' : x*y*z ≠ 0) :
    x^2 * (1 - b^2) = y^2 * (1 - a^2) ∧ y^2 * (1 - a^2) = x*y*(a*b - c) ∧ a^2 + b^2 + c^2 - 2*a*b*c = 1 := by

  have hx1 : x ≠ 0 := by
    by_contra h1
    have h1' : x = 0 := by linarith
    rw [h1'] at h'''
    simp at h'''
  
  have hy1 : y ≠ 0 := by
    by_contra h1
    have h1' : y = 0 := by linarith
    rw [h1'] at h'''
    simp at h'''
  
  have hz1 : z ≠ 0 := by
    by_contra h1
    have h1' : z = 0 := by linarith
    rw [h1'] at h'''
    simp at h'''

  constructor
  · -- Show x^2 * (1 - b^2) = y^2 * (1 - a^2)
    have h1 : x^2 * (1 - b^2) = y^2 * (1 - a^2) := by
      have eq1 : a = (x^2 - y^2 - z^2) / (2 * y * z) := by
        have h1 : (2 * y * z) ≠ 0 := by
          apply mul_ne_zero
          apply mul_ne_zero
          exact two_ne_zero
          exact hy1
          exact hz1
        field_simp [h1]
        nlinarith [h, sq_pos_of_ne_zero (show y ≠ 0 by assumption), sq_pos_of_ne_zero (show z ≠ 0 by assumption)]
      have eq2 : b = (-x^2 + y^2 - z^2) / (2 * x * z) := by
        have h2 : (2 * x * z) ≠ 0 := by
          apply mul_ne_zero
          apply mul_ne_zero
          exact two_ne_zero
          exact hx1
          exact hz1
        field_simp [h2]
        nlinarith [h', sq_pos_of_ne_zero (show x ≠ 0 by assumption), sq_pos_of_ne_zero (show z ≠ 0 by assumption)]
      rw [eq1, eq2]
      field_simp [(show x * z ≠ 0 by apply mul_ne_zero hx1 hz1), (show y * z ≠ 0 by apply mul_ne_zero hy1 hz1)]
      <;> nlinarith [sq_pos_of_ne_zero (show x ≠ 0 by assumption), sq_pos_of_ne_zero (show y ≠ 0 by assumption), sq_pos_of_ne_zero (show z ≠ 0 by assumption), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (a * y * z), sq_nonneg (b * z * x), sq_nonneg (c * x * y)]
    linarith
  constructor
  · -- Show y^2 * (1 - a^2) = x*y*(a*b - c)
    have h2 : y^2 * (1 - a^2) = x*y*(a*b - c) := by
      have eq1 : a = (x^2 - y^2 - z^2) / (2 * y * z) := by
        have h1 : (2 * y * z) ≠ 0 := by
          apply mul_ne_zero
          apply mul_ne_zero
          exact two_ne_zero
          exact hy1
          exact hz1
        field_simp [h1]
        nlinarith [h, sq_pos_of_ne_zero (show y ≠ 0 by assumption), sq_pos_of_ne_zero (show z ≠ 0 by assumption)]
      have eq2 : b = (-x^2 + y^2 - z^2) / (2 * x * z) := by
        have h2 : (2 * x * z) ≠ 0 := by
          apply mul_ne_zero
          apply mul_ne_zero
          exact two_ne_zero
          exact hx1
          exact hz1
        field_simp [h2]
        nlinarith [h', sq_pos_of_ne_zero (show x ≠ 0 by assumption), sq_pos_of_ne_zero (show z ≠ 0 by assumption)]
      have eq3 : c = (-x^2 - y^2 + z^2) / (2 * x * y) := by
        have h3 : (2 * x * y) ≠ 0 := by
          apply mul_ne_zero
          apply mul_ne_zero
          exact two_ne_zero
          exact hx1
          exact hy1
        field_simp [h3]
        nlinarith [h'', sq_pos_of_ne_zero (show x ≠ 0 by assumption), sq_pos_of_ne_zero (show y ≠ 0 by assumption)]
      rw [eq1, eq2, eq3]
      field_simp [(show x * z ≠ 0 by apply mul_ne_zero hx1 hz1), (show y * z ≠ 0 by apply mul_ne_zero hy1 hz1), (show x * y ≠ 0 by apply mul_ne_zero hx1 hy1)]
      <;> nlinarith [sq_pos_of_ne_zero (show x ≠ 0 by assumption), sq_pos_of_ne_zero (show y ≠ 0 by assumption), sq_pos_of_ne_zero (show z ≠ 0 by assumption), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (a * y * z), sq_nonneg (b * z * x), sq_nonneg (c * x * y)]
    linarith
  · -- Show a^2 + b^2 + c^2 - 2*a*b*c = 1
    have h3 : a^2 + b^2 + c^2 - 2*a*b*c = 1 := by
      have eq1 : a = (x^2 - y^2 - z^2) / (2 * y * z) := by
        have h1 : (2 * y * z) ≠ 0 := by
          apply mul_ne_zero
          apply mul_ne_zero
          exact two_ne_zero
          exact hy1
          exact hz1
        field_simp [h1]
        nlinarith [h, sq_pos_of_ne_zero (show y ≠ 0 by assumption), sq_pos_of_ne_zero (show z ≠ 0 by assumption)]
      have eq2 : b = (-x^2 + y^2 - z^2) / (2 * x * z) := by
        have h2 : (2 * x * z) ≠ 0 := by
          apply mul_ne_zero
          apply mul_ne_zero
          exact two_ne_zero
          exact hx1
          exact hz1
        field_simp [h2]
        nlinarith [h', sq_pos_of_ne_zero (show x ≠ 0 by assumption), sq_pos_of_ne_zero (show z ≠ 0 by assumption)]
      have eq3 : c = (-x^2 - y^2 + z^2) / (2 * x * y) := by
        have h3 : (2 * x * y) ≠ 0 := by
          apply mul_ne_zero
          apply mul_ne_zero
          exact two_ne_zero
          exact hx1
          exact hy1
        field_simp [h3]
        nlinarith [h'', sq_pos_of_ne_zero (show x ≠ 0 by assumption), sq_pos_of_ne_zero (show y ≠ 0 by assumption)]
      rw [eq1, eq2, eq3]
      field_simp [(show x * z ≠ 0 by apply mul_ne_zero hx1 hz1), (show y * z ≠ 0 by apply mul_ne_zero hy1 hz1), (show x * y ≠ 0 by apply mul_ne_zero hx1 hy1)]
      <;> nlinarith [sq_pos_of_ne_zero (show x ≠ 0 by assumption), sq_pos_of_ne_zero (show y ≠ 0 by assumption), sq_pos_of_ne_zero (show z ≠ 0 by assumption), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (a * y * z), sq_nonneg (b * z * x), sq_nonneg (c * x * y)]
    linarith