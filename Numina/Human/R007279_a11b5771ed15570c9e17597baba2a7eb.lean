import Mathlib

/- Let $f$, $g$, and $h$ be polynomials such that $h(x) = f(x)\cdot g(x)$.  If the constant term of $f(x)$ is $-4$ and the constant term of $h(x)$ is 3, what is $g(0)$? -/
theorem algebra_16280 {f g h : Polynomial ℝ} (hf : f.coeff 0 = -4) (hh : h.coeff 0 = 3)
    (hfg : h = f * g) :
    g.eval 0 = -3 / 4 := by
  simp [Polynomial.coeff_zero_eq_eval_zero] at *
  apply_fun (fun p => p.eval 0) at hfg
  simp [hf, hh] at hfg
  linear_combination hfg / 4
