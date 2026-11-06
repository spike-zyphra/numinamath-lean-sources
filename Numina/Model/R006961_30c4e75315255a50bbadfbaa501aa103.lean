import Mathlib

theorem algebra_20147 {Q E D : ℂ} (hQ : Q = 11 - 5 * .I) (hE : E = 11 + 5 * .I)

    (hD : D = 2 * .I) : Q * E * D = 292 * .I := by
  rw [hQ, hE, hD]
  simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, pow_two, mul_add, mul_comm, mul_assoc]
  all_goals norm_num