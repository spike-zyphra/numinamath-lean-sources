import Mathlib

theorem algebra_14261 {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a^2 + a * b + b^2 = 0) : (a^9 + b^9) / (a + b)^9 = -2 := by
  have h1 : a^2 = - a * b - b^2 := by
    have eq1 : a^2 + a * b + b^2 = 0 := h
    have eq2 : a^2 = - a * b - b^2 := by
      calc
        a^2 = a^2 + a * b + b^2 - a * b - b^2 := by ring
        _ = 0 - a * b - b^2 := by rw [eq1]
        _ = - a * b - b^2 := by ring
    exact_mod_cast eq2
  have h2 : a^3 = b^3 := by
    calc
      a^3 = a * a^2 := by ring
      _ = a * (- a * b - b^2) := by rw [h1]
      _ = - a^2 * b - a * b^2 := by ring
      _ = - (- a * b - b^2 ) * b - a * b^2 := by rw [h1]
      _ = b^3 := by ring_nf
  have h3 : a^9 = b^9 := by
    calc
      a^9 = (a^3) ^ 3 := by ring
      _ = (b^3) ^ 3 := by rw [h2]
      _ = b^9 := by ring
  have eq1 : a^9 + b^9 = 2 * b^9 := by
    rw [h3]
    ring
  have h4 : (a + b) ^ 3 = - b^3 := by
    have eq1 : (a + b) ^ 3 = a ^ 3 + 3 * a^2 * b + 3 * a * b^2 + b^3 := by
      ring
    rw [eq1, h2, h1]
    ring_nf
  have h5 : (a + b) ^ 9 = -b^9 := by
    calc
      (a + b) ^ 9 = ((a + b) ^ 3) ^ 3 := by ring
      _ = (-b^3) ^ 3 := by rw [h4]
      _ = -b^9 := by ring_nf
  rw [eq1, h5]
  have eq2 : b^9 ≠ 0 := by 
    have h1 : b ≠ 0 := hb
    have h2 : b^9 ≠ 0 := by
      apply pow_ne_zero 9 h1
    exact_mod_cast h2
  field_simp [eq2]
  all_goals ring_nf <;> norm_num