import Mathlib

theorem algebra_4952 {z : ℂ} (hz : z ≠ 0) :
    z^3 = 1 / z ↔ z = 1 ∨ z = Complex.I ∨ z = -1 ∨ z = -Complex.I := by
  constructor
  · -- Assume z^3 = 1 / z, prove z = 1 ∨ z = I ∨ z = -1 ∨ z = -I
    intro h
    have h1 : z ^ 4 = 1 := by
      have h2 : z ≠ 0 := hz
      field_simp [h2] at h ⊢
      <;> ring_nf at h ⊢
      <;> norm_num [Complex.ext_iff] at h ⊢
      <;> tauto
    have h2 : z ^ 4 - 1 = 0 := by
      rw [h1]
      ring_nf
      <;> norm_num [Complex.ext_iff]
    have h3 : (z ^ 2 - 1) * (z ^ 2 + 1) = 0 := by
      have h4 : z ^ 4 - 1 = 0 := h2
      have h5 : (z ^ 2 - 1) * (z ^ 2 + 1) = 0 := by
        have h7 : (z ^ 2 - 1) * (z ^ 2 + 1) = z ^ 4 - 1 := by ring
        rw [h7]
        exact h4
      simpa using h5
    cases (mul_eq_zero.mp h3) with
    | inl h4 =>
      have h5 : z ^ 2 - 1 = 0 := h4
      have h9 : z ^ 2 = 1 := by
        calc
          z ^ 2 = z ^ 2 - 1 + 1 := by ring
          _ = 1 := by rw [h5]; ring
      have h7 : z = 1 ∨ z = -1 := by
        have h10 : z ^ 2 = 1 := h9
        have : z = 1 ∨ z = -1 := by
          have h10 : z ^ 2 = 1 := h10
          rw [sq_eq_one_iff] at h10
          exact h10
        exact this
      cases h7 with
      | inl h8 =>
        -- Case z = 1
        simp [h8]
      | inr h8 =>
        -- Case z = -1
        simp [h8]
        <;> norm_num [Complex.ext_iff] at *
    | inr h5 =>
      have h8 : z ^ 2 + 1 = 0 := h5
      have h9 : z ^ 2 = -1 := by
        calc
          z ^ 2 = z ^ 2 + 1 - 1 := by ring
          _ = -1 := by rw [h8]; ring
      have h11 : z = Complex.I ∨ z = -Complex.I := by
        have h11 : z ^ 2 + 1 = 0 := h8
        have h18 : (z - Complex.I) * (z + Complex.I) = 0 := by
          have h19 : z ^ 2 + 1 = 0 := h8
          have h20 : (z - Complex.I) * (z + Complex.I) = z^2 + 1 := by
            simp [Complex.ext_iff, pow_two, Complex.I_mul_I]
            <;> ring_nf <;> simp [Complex.I_sq]
            <;> ring
          rw [h20]
          exact h19
        cases (mul_eq_zero.mp h18) with
        | inl h21 =>
          left
          have : z = Complex.I := by
            have h22 : z - Complex.I = 0 := h21
            have h23 : z = Complex.I := by
              calc
                z = (z - Complex.I) + Complex.I := by ring
                _ = 0 + Complex.I := by rw [h22]
                _ = Complex.I := by ring
            exact h23
          exact this
        | inr h22 =>
          right
          have : z = -Complex.I := by
            have h23 : z + Complex.I = 0 := h22
            have h24 : z = -Complex.I := by
              calc
                z = (z + Complex.I) - Complex.I := by ring
                _ = (0) - Complex.I := by rw [h23]
                _ = -Complex.I := by ring
            exact h24
          exact this
      cases h11 with
      | inl h12 =>
        -- Case z = i
        simp [h12]
        <;> norm_num [Complex.ext_iff]
      | inr h12 =>
        -- Case z = -i
        simp [h12]
        <;> norm_num [Complex.ext_iff]
  · -- Assume z = 1 ∨ z = I ∨ z = -1 ∨ z = -I, prove z^3 = 1 / z
    rintro (h | h | h | h)
    · -- z = 1
      rw [h]
      field_simp
      <;> norm_num
    · -- z = i
      rw [h]
      field_simp [Complex.ext_iff, pow_two, pow_succ, Complex.I_mul_I]
      <;> norm_num [Complex.I_sq]
      <;> ring_nf <;> norm_num [Complex.I_sq]
      all_goals norm_num [Complex.ext_iff]
    · -- z = -1
      rw [h]
      field_simp
      <;> norm_num
    · -- z = -i
      rw [h]
      field_simp [Complex.ext_iff, pow_two, pow_succ, Complex.I_mul_I]
      <;> norm_num [Complex.I_sq]
      all_goals ring_nf
      all_goals norm_num [Complex.ext_iff]
      all_goals ring