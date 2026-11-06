import Mathlib

theorem algebra_6575 {r s t : ℝ} (P : ℝ → ℝ) (hP : P = fun x => x^3 + x^2 - r^2 * x - 2020)
    (hroots : P r = 0 ∧ P s = 0 ∧ P t = 0) :
    P 1 = -4038 := by
  have hr : P r = 0 := hroots.1
  rw [hP] at hr
  simp at hr
  have r2_eq : r^2 = 2020 := by
    nlinarith [sq_nonneg r, sq_nonneg (r + 1), sq_nonneg (r - 1)]
  have h1 : P 1 = 1^3 + 1^2 - r^2 * 1 - 2020 := by
    rw [hP]
  rw [h1]
  rw [show r^2 = 2020 by linarith [r2_eq]]
  norm_num