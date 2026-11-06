import Mathlib

theorem algebra_189854 {a b c m : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hsum : a + b + c = m) (hsumsq : a^2 + b^2 + c^2 = m^2 / 2) :
    (a * (m - 2 * a)^2 + b * (m - 2 * b)^2 + c * (m - 2 * c)^2) / (a * b * c) = 12 := by
  have h1 : a * b * c ≠ 0 := by
    apply mul_ne_zero
    apply mul_ne_zero
    exact ha
    exact hb
    exact hc
  have h2 : a * b + a * c + b * c = m^2 / 4 := by
    have h : (a + b + c) ^ 2 = a^2 + b^2 + c^2 + 2 * (a * b + a * c + b * c) := by 
      ring 
    rw [hsum, hsumsq] at h 
    linarith 
  have h7 : a^3 + b^3 + c^3 = m^3 / 4 + 3 * (a * b * c) := by 
    have h8 : a^3 + b^3 + c^3 = (a + b + c)^3 - 3 * (a * b + a * c + b * c) * (a + b + c) + 3 * (a * b * c) := by 
      ring 
    rw [h8, hsum, h2] 
    ring
  have h4 : a * (m - 2 * a)^2 + b * (m - 2 * b)^2 + c * (m - 2 * c)^2 = 12 * (a * b * c) := by
    have eq4 : a * (m - 2 * a)^2 + b * (m - 2 * b)^2 + c * (m - 2 * c)^2 =
      m^2 * (a + b + c) - 4 * m * (a^2 + b^2 + c^2) + 4 * (a^3 + b^3 + c^3) := by
      ring_nf
    rw [eq4]
    rw [hsum] at *
    rw [hsumsq]
    rw [h7]
    ring
  have h5 : (a * (m - 2 * a)^2 + b * (m - 2 * b)^2 + c * (m - 2 * c)^2) / (a * b * c) = 12 := by 
    rw [h4]
    field_simp [h1]
  exact h5