import Mathlib

theorem algebra_15226 : {z : ℂ | z^3 = -8} = {-2, 1 + Complex.I * Real.sqrt 3, 1 - Complex.I * Real.sqrt 3} := by 
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- Assume z^3 = -8, prove z ∈ {-2, 1 ± i√3}
    intro h
    have h1 : z^3 + 8 = 0 := by 
      calc
        z^3 + 8 = z^3 + (8 : ℂ) := by norm_num
        _ = (-8 : ℂ) + (8 : ℂ) := by rw [h]
        _ = 0 := by norm_num
    have h2 : z^3 + 8 = (z + 2) * (z^2 - 2 * z + 4) := by
      ring_nf
    rw [h2] at h1
    cases' (mul_eq_zero.mp h1) with h3 h4
    · -- Case z + 2 = 0
      have h5 : z = -2 := by
        have h6 : z + 2 = 0 := h3 
        calc 
          z = (z + 2) - 2 := by ring
          _ = (0) - 2 := by rw [h6]
          _ = -2 := by ring
      left
      exact h5
    · -- Case z^2 - 2 * z + 4 = 0
      have h7 : z^2 - 2 * z + 4 = 0 := h4 
      have h8 : z^2 - 2 * z + 4 = (z - (1 + Complex.I * Real.sqrt 3)) * (z - (1 - Complex.I * Real.sqrt 3)) := by
        ring_nf
        simp [Complex.ext_iff, pow_two, Complex.I_mul_I, mul_add, mul_sub]
        <;> ring_nf <;> norm_num
      rw [h8] at h7 
      cases' (mul_eq_zero.mp h7) with h9 h10
      · -- Case z - (1 + I * sqrt 3) = 0 
        have h11 : z = 1 + Complex.I * Real.sqrt 3 := by
          have h12 : z - (1 + Complex.I * Real.sqrt 3) = 0 := h9
          calc 
            z = (z - (1 + Complex.I * Real.sqrt 3)) + (1 + Complex.I * Real.sqrt 3) := by ring
            _ = (1 + Complex.I * Real.sqrt 3) := by 
              rw [h12]
              <;> ring
        right
        left
        exact h11
      · -- Case z - (1 - I * sqrt 3) = 0
        have h12 : z = 1 - Complex.I * Real.sqrt 3 := by
          have h13 : z - (1 - Complex.I * Real.sqrt 3) = 0 := h10
          calc 
            z = (z - (1 - Complex.I * Real.sqrt 3)) + (1 - Complex.I * Real.sqrt 3) := by ring
            _ = (1 - Complex.I * Real.sqrt 3) := by 
              rw [h13]
              <;> ring
        right
        right
        exact h12
  · -- Assume z ∈ {-2, 1 ± i√3}, prove z^3 = -8
    rintro (h | h | h)
    · -- z = -2 
      rw [h]
      norm_num
    · -- z = 1 + I * sqrt 3 
      rw [h]
      simp [pow_three]
      field_simp [Complex.ext_iff, pow_two, Complex.I_mul_I, mul_add, add_mul]
      <;> ring_nf <;> norm_num
    · -- z = 1 - I * sqrt 3 
      rw [h]
      simp [pow_three]
      field_simp [Complex.ext_iff, pow_two, Complex.I_mul_I, mul_add, add_mul]
      <;> ring_nf <;> norm_num