import Mathlib

theorem algebra_168829 (z1 z2 z3 : ℂ) (hz1 : ‖z1‖ = Real.sqrt 2) (hz2 : ‖z2‖ = Real.sqrt 2)
    (hzz : (z1.re * z2.re + z1.im * z2.im) = 0) (hzz' : ‖z1 + z2 - z3‖ = 2) :
    ‖z3‖ ≤ 4 ∧ ‖z3‖ ≥ 0 := by
  have h3 : ‖z1 + z2‖ = 2 := by
    have h4 : ‖z1 + z2‖ = Real.sqrt ((z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2) := by
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
      <;> ring_nf
    rw [h4]
    have h5 : (z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2 = 4 := by
      have h8 : z1.re ^ 2 + z1.im ^ 2 = 2 := by
        have hz1' : ‖z1‖ = Real.sqrt 2 := hz1
        have h9 : ‖z1‖ = Real.sqrt (z1.re ^ 2 + z1.im ^ 2) := by
          simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
          <;> ring_nf
        rw [h9] at hz1'
        have h11 : z1.re ^ 2 + z1.im ^ 2 = 2 := by
          have h12 : Real.sqrt (z1.re ^ 2 + z1.im ^ 2) = Real.sqrt 2 := hz1'
          have h13 : z1.re ^ 2 + z1.im ^ 2 = 2 := by
            rw [Real.sqrt_inj (by positivity) (by positivity) ] at h12
            linarith
          linarith
        linarith
      have h9 : z2.re ^ 2 + z2.im ^ 2 = 2 := by
        have hz2' : ‖z2‖ = Real.sqrt 2 := hz2
        have h10 : ‖z2‖ = Real.sqrt (z2.re ^ 2 + z2.im ^ 2) := by
          simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
          <;> ring_nf
        rw [h10] at hz2'
        have h11 : z2.re ^ 2 + z2.im ^ 2 = 2 := by
          have h12 : Real.sqrt (z2.re ^ 2 + z2.im ^ 2) = Real.sqrt 2 := hz2'
          have h14 : z2.re ^ 2 + z2.im ^ 2 = 2 := by
            rw [Real.sqrt_inj (by positivity) (by positivity) ] at h12
            linarith
          linarith
        linarith
      calc
        (z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2
          = (z1.re ^ 2 + z2.re ^ 2 + 2 * (z1.re * z2.re)) + (z1.im ^ 2 + z2.im ^ 2 + 2 * (z1.im * z2.im)) := by ring_nf
        _ = (z1.re ^ 2 + z1.im ^ 2) + (z2.re ^ 2 + z2.im ^ 2) + 2 * (z1.re * z2.re + z1.im * z2.im) := by ring_nf
        _ = 2 + 2 + 2 * (0) := by
          rw [show z1.re ^ 2 + z1.im ^ 2 = 2 by linarith [h8], show z2.re ^ 2 + z2.im ^ 2 = 2 by linarith [h9]]
          <;> simp [hzz]
        _ = 4 := by
          norm_num
    rw [h5]
    have h7 : Real.sqrt (4) = (2 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h7]
  have h4 : ‖z3‖ ≤ 4 := by
    have h5' : ‖z3‖ ≤ ‖z1 + z2‖ + ‖z3 - (z1 + z2)‖ := by
      have h : ‖z3‖ = ‖(z1 + z2) + (z3 - (z1 + z2))‖ := by
        simp [Complex.ext_iff]
        <;> ring_nf
      rw [h]
      apply norm_add_le
    have h6 : ‖z3 - (z1 + z2)‖ = 2 := by
      have h7 : ‖z3 - (z1 + z2)‖ = ‖z1 + z2 - z3‖ := by
        simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
        <;> ring_nf
      rw [h7]
      exact hzz'
    rw [h3, h6] at h5'
    linarith
  have h5 : ‖z3‖ ≥ 0 := by
    positivity
  constructor
  · exact h4
  · exact h5