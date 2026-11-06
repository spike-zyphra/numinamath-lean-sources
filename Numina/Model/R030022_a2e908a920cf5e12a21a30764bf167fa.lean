import Mathlib
theorem algebra_21091 {z : ℂ} (hz : z ≠ 0) (h : z^3 + 1 / z^3 = 52) :
    z + 1 / z = 4 ∨ z + 1 / z = -2 + 3 * .I ∨ z + 1 / z = -2 - 3 * .I := by
  have eq1 : z^3 + 1 / z^3 = (z + 1 / z) ^ 3 - 3 * (z + 1 / z) := by
    field_simp [hz]
    ring
  rw [eq1] at h
  have h1 : (z + 1 / z) ^ 3 - 3 * (z + 1 / z) - 52 = 0 := by
    rw [h]
    all_goals
      ring_nf
  have h2 : (z + 1 / z - 4) * ((z + 1 / z) ^ 2 + 4 * (z + 1 / z) + 13) = 0 := by
    have h3 : (z + 1 / z) ^ 3 - 3 * (z + 1 / z) - 52 = 0 := h1
    calc
      (z + 1 / z - 4) * ((z + 1 / z) ^ 2 + 4 * (z + 1 / z) + 13)
        = (z + 1 / z) ^ 3 - 3 * (z + 1 / z) - 52 := by ring
      _ = 0 := h3
  cases' (mul_eq_zero.mp h2) with h3 h4
  · -- Case h3: z + 1 / z - 4 = 0
    left
    have h5 : z + 1 / z = 4 := by
      calc
        z + 1 / z = (z + 1 / z - 4) + 4 := by ring_nf
        _ = 0 + 4 := by rw [h3]
        _ = 4 := by ring_nf
    exact h5
  · -- Case h4: (z + 1 / z) ^ 2 + 4 * (z + 1 / z) + 13 = 0
    have eq2 : (z + 1 / z) ^ 2 + 4 * (z + 1 / z) + 13 = 0 := h4
    have eq3 : (z + 1 / z - (-2 + 3 * Complex.I)) * (z + 1 / z - (-2 - 3 * Complex.I)) = 0 := by
      have h5 : (z + 1 / z) ^ 2 + 4 * (z + 1 / z) + 13 = 0 := eq2
      have h6 : (z + 1 / z - (-2 + 3 * Complex.I)) * (z + 1 / z - (-2 - 3 * Complex.I)) = (z + 1 / z) ^ 2 + 4 * (z + 1 / z) + 13 := by
        ring_nf
        simp [Complex.I_sq, pow_two]
        <;> ring_nf
        <;> norm_num [Complex.I_sq]
      rw [h6]
      exact h5
    cases' (mul_eq_zero.mp eq3) with h41 h42
    · -- Case h41: z + 1 / z - (-2 + 3 * Complex.I) = 0
      right
      left
      have h5 : z + 1 / z = -2 + 3 * Complex.I := by
        have eq4 : z + 1 / z - (-2 + 3 * Complex.I) = 0 := h41
        calc
          z + 1 / z = (z + 1 / z - (-2 + 3 * Complex.I)) + (-2 + 3 * Complex.I) := by ring_nf
          _ = 0 + (-2 + 3 * Complex.I) := by rw [eq4]
          _ = -2 + 3 * Complex.I := by ring_nf
      exact h5
    · -- Case h42: z + 1 / z - (-2 - 3 * Complex.I) = 0
      right
      right
      have h6 : z + 1 / z = -2 - 3 * Complex.I := by
        have eq5 : z + 1 / z - (-2 - 3 * Complex.I) = 0 := h42
        calc
          z + 1 / z = (z + 1 / z - (-2 - 3 * Complex.I)) + (-2 - 3 * Complex.I) := by ring_nf
          _ = 0 + (-2 - 3 * Complex.I) := by rw [eq5]
          _ = -2 - 3 * Complex.I := by ring_nf
      exact h6