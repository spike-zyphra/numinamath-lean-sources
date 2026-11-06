import Mathlib

theorem algebra_324361 {z1 z2 : ℂ} (hz1 : (z1 - 2) * (1 + Complex.I) = 1 - Complex.I)
    (hz2 : z2.im = 2) :
    (z1 * z2).im = 0 ↔ z2 = 4 + 2 * Complex.I := by

  have h1 : z1 = 2 - Complex.I := by
    have eq1 : (z1 - 2) * (1 + Complex.I) = 1 - Complex.I := hz1
    have eq2 : z1 * (1 + Complex.I) = 3 + Complex.I := by
      calc
        z1 * (1 + Complex.I) = (z1 - 2) * (1 + Complex.I) + 2 * (1 + Complex.I) := by ring_nf
        _ = (1 - Complex.I) + 2 * (1 + Complex.I) := by rw [hz1]
        _ = 3 + Complex.I := by simp [Complex.ext_iff]; all_goals norm_num
    have eq3 : z1 = 2 - Complex.I := by
      have hne : (1 + Complex.I) ≠ 0 := by
        simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im]
      apply (mul_left_inj' hne).mp
      have h2 : (3 + Complex.I) = (2 - Complex.I) * (1 + Complex.I) := by
        simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
        all_goals norm_num
      rw [h2] at eq2
      simpa using eq2
    exact_mod_cast eq3
  rw [h1]
  constructor
  · -- Assume (z1 * z2).im = 0, prove z2 = 4 + 2 * Complex.I
    intro h
    have h2 : ( (2 - Complex.I) * z2 ).im = 0 := h
    have eq1 : z2.im = 2 := hz2
    have eq2 : z2.re = 4 := by
      simp [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.I_im, Complex.I_re, 
        Complex.ofReal_re, Complex.add_re, Complex.mul_re, Complex.I_im] at h2
      ring_nf at h2
      nlinarith [eq1]
    have eq3 : z2 = 4 + 2 * Complex.I := by
      simp [Complex.ext_iff, eq1, eq2]
      all_goals norm_num
    exact_mod_cast eq3
  · -- Assume z2 = 4 + 2 * Complex.I, prove (z1 * z2).im = 0
    intro h
    rw [h]
    simp [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.I_im, Complex.I_re, 
      Complex.ofReal_re, Complex.add_re, Complex.mul_re, Complex.I_im]
    all_goals norm_num