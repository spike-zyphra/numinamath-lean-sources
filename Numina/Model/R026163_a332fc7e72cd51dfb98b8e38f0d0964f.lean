import Mathlib

theorem algebra_302820 {f : MvPolynomial (Fin 2) ℝ} (hf : MvPolynomial.eval ![1, 2] f = 2)
    (hxy : ∀ x y, y * MvPolynomial.eval ![x, y] f = x * MvPolynomial.eval ![x, MvPolynomial.eval ![x, y] f] f)
    (hf' : ∀ x y, x * MvPolynomial.eval ![x, y] f = (MvPolynomial.eval ![x, y] f)^2) :
    f = MvPolynomial.X 0 * MvPolynomial.X 1 := by
  have h1 := hf' 1 2
  rw [hf] at h1
  norm_num at h1
  all_goals
    nlinarith