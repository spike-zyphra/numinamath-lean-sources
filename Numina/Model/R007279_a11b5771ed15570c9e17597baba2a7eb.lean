import Mathlib

theorem algebra_16280 {f g h : Polynomial ℝ} (hf : f.coeff 0 = -4) (hh : h.coeff 0 = 3)
    (hfg : h = f * g) :
    g.eval 0 = -3 / 4 := by
  have eq1 : h.eval 0 = f.eval 0 * g.eval 0 := by
    rw [hfg]
    simp
  have eq2 : h.eval 0 = 3 := by
    simp [Polynomial.eval, hh]
  have eq3 : f.eval 0 = -4 := by
    simp [Polynomial.eval, hf]
  rw [eq2] at eq1
  rw [eq3] at eq1
  linarith