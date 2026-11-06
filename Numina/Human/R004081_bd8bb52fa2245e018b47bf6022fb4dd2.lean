import Mathlib

/-Find all pairs (a,b) of positive rational numbers such that
√a + √b = √(2 + √3).-/
theorem algebra_236558:  {(a,b): ℚ × ℚ | 0 < a ∧ 0 < b ∧ √a + √b = √(2 + √3)} = {(1/2,3/2),(3/2,1/2)} := by
  have sq_3: √3 ^ 2 = 3 := by norm_num
  ext ⟨a,b⟩
  constructor
  -- forward direction --
  . intro h
    simp at h
    rcases h with ⟨ha, hb, h⟩
    replace h: (√a + √b) ^ 2 = 2 + √3 := by
      simp [h]
      symm
      rw [← Real.sqrt_eq_iff_eq_sq]
      nlinarith
      apply Real.sqrt_nonneg
    replace h: a +  b + 2 * Real.sqrt (a * b) = 2 + √3 := by
      have eq: (√a + √b) ^ 2 = a + b + 2 * Real.sqrt (a * b) := by
        ring_nf
        have eqa: (√a) ^ 2 = a := by
          symm
          rw [← Real.sqrt_eq_iff_eq_sq]
          simp
          nlinarith
          apply Real.sqrt_nonneg
        have eqb: (√b) ^ 2 = b := by
          symm
          rw [← Real.sqrt_eq_iff_eq_sq]
          simp
          nlinarith
          apply Real.sqrt_nonneg
        rw [eqa, eqb]
        have eqab:  √a * √b = √(a * b) := by
          have hx: 0 ≤ (a: ℝ) := by simp; linarith
          symm
          apply Real.sqrt_mul hx (b: ℝ)
        rw [eqab]
        ring
      rw [eq] at h
      exact h
    set r:= 2 - a - b with hr
    replace h: 2 * √a * √b = r + √3 := by
      rw [hr]
      simp
      rw [show 2 - ↑a - ↑b + √3 = 2 + √3 - ↑a - ↑b by ring]
      rw [← h]
      ring_nf
      have eqab:  √a * √b = √(a * b) := by
          have hx: 0 ≤ (a: ℝ) := by simp; linarith
          symm
          apply Real.sqrt_mul hx (b: ℝ)
      rw [eqab]
    clear_value r
    replace h: (2 * √a * √b) ^ 2 = (r + √3) ^ 2 := by rw [h]
    have l: (2 * √a * √b) ^ 2 = 4 * a * b := by
      have eqab:  √a * √b = √(a * b) := by
          have hx: 0 ≤ (a: ℝ) := by simp; linarith
          symm
          apply Real.sqrt_mul hx (b: ℝ)
      rw [show (2 * √a * √b) = (2 * (√a * √b)) by ring]
      rw [eqab]
      ring_nf
      simp
      symm
      rw [← Real.sqrt_eq_iff_eq_sq]
      norm_cast
      nlinarith
      apply Real.sqrt_nonneg
    have eq_r:  (r + √3) ^ 2 = r ^ 2 + 3 + 2 * r * √3 := by
      ring_nf
      rw [sq_3]
      ring
    rw [l] at h
    rw [eq_r] at h
    clear l eq_r
    have r0: r = 0 := by    -- now we must have r = 0 --
      by_contra! no
      replace h: 4 * a * b - r ^ 2 - 3 = 2 * r * √3 := by
        nlinarith
      replace h: (4 * a * b - r ^ 2 - 3) / (2 * r) = √3 := by
        rw [h]
        field_simp
      let a:= (4 * a * b - r ^ 2 - 3) / (2 * r)
      replace h: a = √3 := by
        simp [a,h]
      have contra:= Rat.not_irrational a
      rw [h] at contra
      absurd contra
      apply Nat.Prime.irrational_sqrt
      norm_num
    simp [r0] at h
    norm_cast at h
    simp [r0] at hr
    replace hr: a = 2 - b := by linarith
    simp [hr] at h
    ring_nf at h
    replace h: b ^ 2 * 4 - b * 8 + 3 = 0 := by linarith
    have id: b ^ 2 * 4 - b * 8 + 3 = 4 * (b - 3/2) * (b - 1/2) := by
      field_simp
      ring
    simp [id] at h
    rcases h with h | h
    . replace h: b = 3/2 := by linarith
      simp [h] at hr
      simp
      left
      simp [hr,h]
      norm_num
    . replace h: b = 1/2 := by linarith
      simp [h] at hr
      simp
      right
      simp [hr,h]
      norm_num

  -- backward direction --
  . intro h
    simp at h
    simp
    rcases h with h | h
    -- a = 1 /2 --
    . constructor
      . simp [h]
      . constructor
        . simp [h]
        . have eq: (√a + √b) ^ 2 = 2 + √3 := by
            have eq: (√a + √b) ^ 2 = a + b + 2 * Real.sqrt (a * b) := by
                ring_nf
                have eqa: (√a) ^ 2 = a := by
                  symm
                  rw [← Real.sqrt_eq_iff_eq_sq]
                  simp
                  nlinarith
                  apply Real.sqrt_nonneg
                have eqb: (√b) ^ 2 = b := by
                  symm
                  rw [← Real.sqrt_eq_iff_eq_sq]
                  simp
                  nlinarith
                  apply Real.sqrt_nonneg
                rw [eqa, eqb]
                have eqab:  √a * √b = √(a * b) := by
                  have hx: 0 ≤ (a: ℝ) := by simp; linarith
                  symm
                  apply Real.sqrt_mul hx (b: ℝ)
                rw [eqab]
                ring_nf
            rw [eq]
            have l: √(a * b) = √3 / 2 := by
              rw [Real.sqrt_eq_iff_eq_sq]
              have o: (√3 / 2) ^ 2 = 3 / 4 := by
                rw [show (√3 / 2) ^ 2 = (√3) ^ 2 / (2 ^ 2) by ring]
                rw [sq_3]
                norm_num
              rw [o]
              simp [h]
              field_simp
              norm_num
              simp [h]
              norm_num
              have i:= Real.sqrt_nonneg 3
              nlinarith
            rw [l]
            ring_nf
            simp [h]
            norm_num
          symm
          rw [Real.sqrt_eq_iff_eq_sq]
          . rw [eq]
          . nlinarith
          . have ha:= Real.sqrt_nonneg a
            have hb:= Real.sqrt_nonneg b
            nlinarith
    -- b = 1 / 2, similar --
    . constructor
      . simp [h]
      . constructor
        . simp [h]
        . have eq: (√a + √b) ^ 2 = 2 + √3 := by
            have eq: (√a + √b) ^ 2 = a + b + 2 * Real.sqrt (a * b) := by
                ring_nf
                have eqa: (√a) ^ 2 = a := by
                  symm
                  rw [← Real.sqrt_eq_iff_eq_sq]
                  simp
                  nlinarith
                  apply Real.sqrt_nonneg
                have eqb: (√b) ^ 2 = b := by
                  symm
                  rw [← Real.sqrt_eq_iff_eq_sq]
                  simp
                  nlinarith
                  apply Real.sqrt_nonneg
                rw [eqa, eqb]
                have eqab:  √a * √b = √(a * b) := by
                  have hx: 0 ≤ (a: ℝ) := by simp; linarith
                  symm
                  apply Real.sqrt_mul hx (b: ℝ)
                rw [eqab]
                ring_nf
            rw [eq]
            have l: √(a * b) = √3 / 2 := by
              rw [Real.sqrt_eq_iff_eq_sq]
              have o: (√3 / 2) ^ 2 = 3 / 4 := by
                rw [show (√3 / 2) ^ 2 = (√3) ^ 2 / (2 ^ 2) by ring]
                rw [sq_3]
                norm_num
              rw [o]
              simp [h]
              field_simp
              norm_num
              simp [h]
              have i:= Real.sqrt_nonneg 3
              nlinarith
            rw [l]
            ring_nf
            simp [h]
            norm_num
          symm
          rw [Real.sqrt_eq_iff_eq_sq]
          . rw [eq]
          . nlinarith
          . have ha:= Real.sqrt_nonneg a
            have hb:= Real.sqrt_nonneg b
            nlinarith
