import Mathlib

theorem algebra_180816 (x : ℂ) (hx : x = -2 ∨ x = 4 - 3 * .I) :
    x^3 - 6 * x^2 + 9 * x + 50 = 0 := by 
  rcases hx with (rfl | rfl)
  · -- First case where x = -2
    norm_num [pow_two, pow_three, Complex.ext_iff]
  · -- Second case where x = 4 - 3i
    simp [pow_two, pow_three, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    all_goals norm_num
    <;> ring_nf <;> norm_num