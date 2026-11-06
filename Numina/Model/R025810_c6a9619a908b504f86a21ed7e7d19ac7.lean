import Mathlib

theorem algebra_162402 {f g : Polynomial ℝ} (hf : f = X^3 - 3*X^2 - 4*X + 4)
    (hg : g = X^3 + a*X^2 + b*X + c) (r s : Fin 3 → ℝ)
    (hr : ∀ i, f.eval (r i) = 0) (hs : ∀ i, g.eval (s i) = 0)
    (hroots : ∀ i, s i = r i + r (i + 1) * z + r (i + 2) * z^2)
    (hz : z = (-1 + Complex.I * Real.sqrt 3) / 2) :
    g.coeff 0 + g.coeff 1 + g.coeff 2 = -26 := by 
  have h1 := hs 0
  have h2 := hs 1
  have h3 := hs 2
  simp [hg] at h1 h2 h3
  have h4 := hroots 0
  have h5 := hroots 1
  have h6 := hroots 2
  simp [hf] at hr
  simp [hroots] at h4 h5 h6
  norm_num [Complex.ext_iff] at hz 
  all_goals 
    norm_num [hz] at h4 h5 h6 
    all_goals 
      ring_nf at h1 h2 h3 h4 h5 h6 
      all_goals 
        ring_nf at *
        <;> nlinarith [sq_nonneg (r 0), sq_nonneg (r 1), sq_nonneg (r 2), sq_nonneg (r 0 - r 1), sq_nonneg (r 1 - r 2), sq_nonneg (r 0 - r 2), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]