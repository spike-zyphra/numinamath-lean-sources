import Mathlib

theorem algebra_319429 {z : ℂ} (hz : z^2 + z + 1 = 0) :
    z^2005 = -1 / 2 + √3 / 2 * .I ∨ z^2005 = -1 / 2 - √3 / 2 * .I := by
  have h1 : z ^ 3 = 1 := by
    have eq2 : z ^ 3 - 1 = 0 := by
      calc
        z ^ 3 - 1 = (z - 1) * (z^2 + z + 1) := by ring_nf
        _ = (z - 1) * (0) := by rw [hz]
        _ = 0 := by ring_nf
    have eq3 : z ^ 3 = 1 := by
      have h3 : z^3 - 1 = 0 := eq2
      have h4 : z^3 = 1 := by
        have eq5 : z^3 - 1 = 0 := h3
        have eq6 : z^3 = 1 := by
          have h5 : z^3 - 1 = 0 := eq5
          have h6 : z^3 = 1 := by
            calc
              z^3 = (z^3 - 1) + 1 := by ring_nf
              _ = 0 + 1 := by rw [h5]
              _ = 1 := by ring_nf
          exact h6
        exact eq6
      exact h4
    exact eq3
  have eq7 : z^2005 = z := by
    calc
      z^2005 = z^(3 * 668 + 1) := by norm_num
      _ = (z^3) ^ 668 * z := by ring_nf
      _ = (1) ^ 668 * z := by rw [h1]
      _ = 1 ^ 668 * z := by rfl
      _ = 1 * z := by norm_num
      _ = z := by ring_nf
  have h3 : z = -1 / 2 + √3 / 2 * Complex.I ∨ z = -1 / 2 - √3 / 2 * Complex.I := by
    have h4 : z^2 + z + 1 = 0 := hz
    have h5 : z^2 + z + 1 = (z - (-1/2 + √3/2 * Complex.I)) * (z - (-1/2 - √3/2 * Complex.I)) := by
      ring_nf
      simp [Complex.ext_iff, pow_two, Complex.I_mul_I, mul_add, sub_eq_zero]
      <;> ring_nf <;> norm_num [Complex.I_sq]
      <;> ring
    rw [h5] at h4
    cases (mul_eq_zero.1 h4) with
    | inl h6 => 
      left
      exact eq_of_sub_eq_zero h6
    | inr h7 => 
      right
      exact eq_of_sub_eq_zero h7
  cases h3 with
  | inl h4 => 
    left
    rw [eq7]
    exact h4
  | inr h5 => 
    right
    rw [eq7]
    exact h5