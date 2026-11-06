import Mathlib

theorem algebra_255608 {z : ℂ} (hz : z ≠ 0) :
    Complex.abs z = 1 / Complex.abs z ∧ Complex.abs z = Complex.abs (z - 1) ↔
    z = (1 / 2) + Complex.I * (Real.sqrt 3 / 2) ∨ z = (1 / 2) - Complex.I * (Real.sqrt 3 / 2) := by

  constructor
  · -- Assume the conditions hold, derive the possible values of z
    intro h
    rcases h with ⟨h1, h2⟩

    have h3 : Complex.abs z > 0 := by
      have h4 : Complex.abs z ≥ 0 := by positivity
      by_contra h5
      push_neg at h5
      have h6 : Complex.abs z = 0 := by linarith
      have h7 : z = 0 := by
        simpa using h6
      contradiction

    have h4 : Complex.abs z = 1 := by
      field_simp [h3] at h1
      nlinarith

    have h5 : Complex.abs (z - 1) = 1 := by
      linarith [h4, h2]

    have h8 : Complex.abs z = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf
      <;> simp [add_sq]
      all_goals ring_nf
      all_goals simp

    have h9 : Complex.abs (z - 1) = Real.sqrt ((z.re - 1) ^ 2 + z.im ^ 2) := by
      have h10 : (z - 1 : ℂ) = (z.re - 1) + z.im * Complex.I := by
        simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
        <;> ring_nf
        <;> simp
        <;> ring_nf
        <;> simp
      rw [h10]
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf
      <;> simp [add_sq]
      all_goals ring_nf <;> simp

    have h10 : z.re ^ 2 + z.im ^ 2 = 1 := by
      calc
        z.re ^ 2 + z.im ^ 2 = (Real.sqrt (z.re ^ 2 + z.im ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
        _ = (Complex.abs z) ^ 2 := by rw [h8]
        _ = 1 ^ 2 := by rw [h4]
        _ = 1 := by norm_num

    have h11 : (z.re - 1) ^ 2 + z.im ^ 2 = 1 := by
      calc
        (z.re - 1) ^ 2 + z.im ^ 2 = (Real.sqrt ((z.re - 1) ^ 2 + z.im ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
        _ = (Complex.abs (z - 1)) ^ 2 := by rw [h9]
        _ = 1 ^ 2 := by rw [h5]
        _ = 1 := by norm_num

    have h12 : z.re = 1 / 2 := by
      nlinarith

    have h13 : z.im ^ 2 = 3 / 4 := by
      rw [h12] at h10
      nlinarith

    have h14 : z.im = Real.sqrt 3 / 2 ∨ z.im = - Real.sqrt 3 / 2 := by
      have h15 : z.im ^ 2 - 3 / 4 = 0 := by
        nlinarith
      have h16 : z.im ^ 2 - 3 / 4 = (z.im - Real.sqrt 3 / 2) * (z.im + Real.sqrt 3 / 2) := by
        ring_nf
        rw [Real.sq_sqrt (by norm_num)]
        <;> nlinarith
        all_goals linarith
        all_goals norm_num
      rw [h16] at h15
      cases (mul_eq_zero.1 h15) with
      | inl h17 =>
        left
        linarith
      | inr h18 =>
        right
        nlinarith

    rcases h14 with h15 | h16
    · -- Case where z.im = √3/2
      left
      simp [Complex.ext_iff, h12, h15]
      <;> ring_nf <;> norm_num [Real.sqrt_pos.mpr]
      all_goals nlinarith
    · -- Case where z.im = -√3/2
      right
      simp [Complex.ext_iff, h12, h16]
      <;> ring_nf <;> norm_num [Real.sqrt_pos.mpr]
      all_goals nlinarith

  · -- Assume z equals either solution, prove the conditions hold
    rintro (h | h)
    · -- First solution
      rw [h]
      constructor
      · -- First condition: |z| = 1/|z|
        have hz1 : Complex.abs ((1 / 2 : ℂ) + Complex.I * (Real.sqrt 3 / 2)) = 1 := by
          simp [Complex.abs, Complex.normSq, Complex.I_re, Complex.I_im]
          ring_nf
          rw [Real.sq_sqrt (by norm_num)]
          all_goals norm_num
        rw [hz1]
        field_simp [hz1]
        all_goals norm_num
        all_goals positivity
      · -- Second condition: |z| = |z - 1|
        have hz1 : Complex.abs ((1 / 2 : ℂ) + Complex.I * (Real.sqrt 3 / 2)) = 1 := by
          simp [Complex.abs, Complex.normSq, Complex.I_re, Complex.I_im]
          ring_nf
          rw [Real.sq_sqrt (by norm_num)]
          all_goals norm_num
        have hz2 : Complex.abs ((1 / 2 : ℂ) + Complex.I * (Real.sqrt 3 / 2) - 1) = 1 := by
          simp [Complex.abs, Complex.normSq, Complex.I_re, Complex.I_im]
          ring_nf
          rw [Real.sq_sqrt (by norm_num)]
          all_goals norm_num
        rw [hz1, hz2]
        all_goals norm_num
    · -- Second solution
      rw [h]
      constructor
      · -- First condition: |z| = 1/|z|
        have hz1 : Complex.abs ((1 / 2 : ℂ) - Complex.I * (Real.sqrt 3 / 2)) = 1 := by
          simp [Complex.abs, Complex.normSq, Complex.I_re, Complex.I_im]
          ring_nf
          rw [Real.sq_sqrt (by norm_num)]
          all_goals norm_num
        rw [hz1]
        field_simp [hz1]
        all_goals norm_num
        all_goals positivity
      · -- Second condition: |z| = |z - 1|
        have hz1 : Complex.abs ((1 / 2 : ℂ) - Complex.I * (Real.sqrt 3 / 2)) = 1 := by
          simp [Complex.abs, Complex.normSq, Complex.I_re, Complex.I_im]
          ring_nf
          rw [Real.sq_sqrt (by norm_num)]
          all_goals norm_num
        have hz2 : Complex.abs ((1 / 2 : ℂ) - Complex.I * (Real.sqrt 3 / 2) - 1) = 1 := by
          simp [Complex.abs, Complex.normSq, Complex.I_re, Complex.I_im]
          ring_nf
          rw [Real.sq_sqrt (by norm_num)]
          all_goals norm_num
        rw [hz1, hz2]
        all_goals norm_num