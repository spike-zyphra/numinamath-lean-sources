import Mathlib

theorem algebra_278932 (z1 z2 : ℂ) (hz1 : Complex.abs z1 = 1) (hz2 : Complex.abs z2 = 1)
    (hsum : z1 + z2 - 1 = 0) :
    (z1 - z2)^2 = -3 := by

  have h1 : z2 = 1 - z1 := by
    have h2 : z2 = 1 - z1 := by
      calc
        z2 = (z1 + z2 - 1) + 1 - z1 := by ring_nf
        _ = 0 + 1 - z1 := by rw [hsum]
        _ = 1 - z1 := by ring_nf
    exact h2

  have eq1 : z1.re ^ 2 + z1.im ^ 2 = 1 := by
    have hz1' : Complex.abs z1 = 1 := hz1
    simp [Complex.abs, Complex.normSq] at hz1' ⊢
    nlinarith

  have eq3 : (1 - z1.re) ^ 2 + z1.im ^ 2 = 1 := by
    have hz2' : Complex.abs (1 - z1) = 1 := by
      have eq4 : z2 = 1 - z1 := h1
      rw [eq4] at hz2
      exact_mod_cast hz2
    simp [Complex.abs, Complex.normSq] at hz2' ⊢
    ring_nf at hz2' ⊢
    nlinarith

  have hx : z1.re = 1 / 2 := by
    nlinarith [eq1, eq3]

  have hy2 : z1.im ^ 2 = 3 / 4 := by
    rw [hx] at eq1
    linarith

  have eq4 : z1 - z2 = 2 * (z1.im * Complex.I) := by
    rw [show z2 = 1 - z1 by simpa using h1]
    have eq4' : z1 - (1 - z1) = 2 * z1 - 1 := by ring_nf
    have eq5 : 2 * z1 - 1 = 2 * (z1.im * Complex.I) := by
      have eq6' : z1 = 1 / 2 + (z1.im * Complex.I) := by
        have eq7' : z1.re = 1 / 2 := hx
        simp [Complex.ext_iff, eq7']
        <;> ring_nf
      rw [eq6']
      ring_nf
      <;> simp [Complex.ext_iff]
      <;> ring_nf
    rw [eq4', eq5]

  rw [eq4]
  have eq6 : (2 * (z1.im * Complex.I)) ^ 2 = (-4 * z1.im ^ 2 : ℂ) := by
    simp [pow_two, mul_pow, Complex.ext_iff, mul_add, mul_comm, mul_left_comm, Complex.I_mul_I]
    <;> ring_nf

  rw [eq6]
  have eq7 : (-4 * z1.im ^ 2 : ℂ) = -3 := by
    have eq8 : (z1.im ^ 2 : ℝ) = (3 / 4 : ℝ) := by
      simpa using hy2
    have eq9 : (-4 * z1.im ^ 2 : ℝ) = -3 := by
      nlinarith [eq8]
    have eq10 : (-4 * z1.im ^ 2 : ℂ) = (-4 * z1.im ^ 2 : ℝ) := by simp
    rw [eq10]
    rw [show (-4 * z1.im ^ 2 : ℝ) = (-3 : ℝ) by linarith [eq9]]
    simp

  exact_mod_cast eq7