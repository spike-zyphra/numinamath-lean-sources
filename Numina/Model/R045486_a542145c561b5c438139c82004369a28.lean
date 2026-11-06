import Mathlib

theorem algebra_269650 {x y z : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (h1 : x + y + z = 0) (h2 : 1 / x + 1 / y + 1 / z = 0) :
    (x^6 + y^6 + z^6) / (x^3 + y^3 + z^3) = x * y * z := by

  have h3 : y * z + x * z + x * y = 0 := by
    field_simp [hx, hy, hz] at h2
    nlinarith

  have h4 : x ^ 3 + y ^ 3 + z ^ 3 = 3 * x * y * z := by
    have eq3 : x ^ 3 + y ^ 3 + z ^ 3 - 3 * x * y * z = (x + y + z) * (x ^ 2 + y ^ 2 + z ^ 2 - (x * y + y * z + z * x)) := by ring
    have eq3a : (x + y + z) * (x ^ 2 + y ^ 2 + z ^ 2 - (x * y + y * z + z * x)) = 0 := by
      have h1' : x + y + z = 0 := h1
      rw [h1']
      norm_num
    linarith [eq3, eq3a]

  have h5 : x^2 + y^2 + z^2 = 0 := by
    have h5a : x * y + y * z + z * x = 0 := by
      nlinarith [h3]
    have eq1 : x ^ 2 + y ^ 2 + z ^ 2 = (x + y + z) ^ 2 - 2 * (x * y + y * z + z * x) := by ring
    rw [h1, h5a] at eq1 
    linarith

  have h7 : x ^ 6 + y ^ 6 + z ^ 6 = 3 * (x * y * z) ^ 2 := by
    have h8 : x ^ 6 + y ^ 6 + z ^ 6 = (x^2)^3 + (y^2)^3 + (z^2)^3 := by ring
    rw [h8]
    have h9 : (x^2)^3 + (y^2)^3 + (z^2)^3 - 3 * (x^2 * y^2 * z^2) = (x^2 + y^2 + z^2) * ((x^2)^2 + (y^2)^2 + (z^2)^2 - (x^2 * y^2 + y^2 * z^2 + z^2 * x^2)) := by ring
    have h10 : (x^2)^2 + (y^2)^2 + (z^2)^2 = (x^2 + y^2 + z^2)^2 - 2 * (x^2 * y^2 + y^2 * z^2 + z^2 * x^2) := by ring
    rw [h10] at h9
    have h11 : x^2 + y^2 + z^2 = 0 := h5
    rw [h11] at h9
    have h12 : x^2 * y^2 + y^2 * z^2 + z^2 * x^2 = 0 := by
      have eq3 : x^2 * y^2 + y^2 * z^2 + z^2 * x^2 = (x * y + y * z + z * x)^2 - 2 * (x * y * z) * (x + y + z) := by ring
      have eq3a : x * y + y * z + z * x = 0 := by
        nlinarith [h3]
      rw [eq3a, h1] at eq3
      linarith
    rw [h12] at h9
    linarith

  have h10 : x^3 + y^3 + z^3 ≠ 0 := by
    by_contra h
    have h11 : x * y * z = 0 := by
      linarith [h4, h]
    cases' (mul_eq_zero.1 h11) with h11 h12
    cases' (mul_eq_zero.1 h11) with h11 h11
    · contradiction
    · contradiction
    · contradiction

  have h11 : (x^6 + y^6 + z^6) = 3 * (x * y * z) ^ 2 := h7

  have h12 : x * y * z ≠ 0 := by
    apply mul_ne_zero
    apply mul_ne_zero
    exact hx
    exact hy
    exact hz

  rw [h11, h4]
  field_simp [h12]
  <;> nlinarith