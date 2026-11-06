import Mathlib

theorem algebra_10536 {Q E D : ℂ} (hQ : Q = 5 + 2 * .I) (hE : E = .I) (hD : D = 5 - 2 * .I) :
    Q * E * D = 29 * .I := by
  rw [hQ, hE, hD]
  simp [Complex.ext_iff, Complex.I_mul_I]
  all_goals norm_num