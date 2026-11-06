import Mathlib

theorem algebra_10855 {z : ℂ} (hz : z = (-Real.sqrt 3 + Complex.I) / 2) :
    z^6 = -1 := by
  rw [hz]
  -- Define necessary square roots facts
  have h1_pos : Real.sqrt 3 > 0 := by positivity
  have h2_sq : Real.sqrt 3 ^ 2 = 3 := by
    rw [Real.sq_sqrt]
    all_goals norm_num
  have h1 : ((-Real.sqrt 3 + Complex.I) / 2 : ℂ) ^ 2 = (1 - Real.sqrt 3 * Complex.I) / 2 := by 
    simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    constructor
    · field_simp [h1_pos]
      nlinarith [h2_sq, Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)]
    · field_simp [h1_pos]
      nlinarith [h2_sq, Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)]
  have h2 : ((-Real.sqrt 3 + Complex.I) / 2 : ℂ) ^ 3 = Complex.I := by
    have eq1 : ((-Real.sqrt 3 + Complex.I) / 2 : ℂ) ^ 3 = ((-Real.sqrt 3 + Complex.I) / 2) * ((-Real.sqrt 3 + Complex.I) / 2 : ℂ) ^ 2 := by
      ring
    rw [eq1]
    rw [h1]
    -- Now compute product, use computational tactics rather than complex algebra
    simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, h2_sq]
    <;> ring_nf 
    <;> norm_num <;> ring_nf
  have h3 : ((-Real.sqrt 3 + Complex.I) / 2 : ℂ) ^ 6 = -1 := by 
    calc
      ((-Real.sqrt 3 + Complex.I) / 2 : ℂ) ^ 6 
        = ((-Real.sqrt 3 + Complex.I) / 2 : ℂ) ^ 3 * ((-Real.sqrt 3 + Complex.I) / 2 : ℂ) ^ 3 := by ring
      _ = (Complex.I : ℂ) * (Complex.I : ℂ) := by rw [h2]
      _ = -1 := by simp [Complex.I_mul_I]
  exact h3