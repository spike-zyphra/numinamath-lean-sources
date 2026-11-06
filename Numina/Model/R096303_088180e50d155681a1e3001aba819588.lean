import Mathlib

/- Given that the polynomial $2{{x}^{2}}+3xy-2{{y}^{2}}-x+8y-6$ can be factored into the form $(x+2y+m)(2x-y+n)$, then the value of $\frac{{{m}^{3}}+1}{{{n}^{2}}-1}$ is ___          ___. -/
theorem algebra_973 {m n : ℝ} (h : ∀ x y : ℝ, 2*x^2+3*x*y-2*y^2-x+8*y-6 = (x+2*y+m)*(2*x-y+n)) :
    (m^3+1)/(n^2-1) = -7/8 := by
  have eq1 := h 0 0
  have eq2 := h 1 0
  have eq3 := h 0 1
  have eq4 := h 1 1
  have h1 : m * n = -6 := by
    nlinarith
  have h2 : (1 + m) * (2 + n) = -5 := by
    nlinarith
  have h3 : (2 + m) * (n - 1) = 0 := by
    nlinarith
  have h4 : (3 + m) * (1 + n) = 4 := by
    nlinarith
  cases' (mul_eq_zero.mp h3) with h5 h6
  · -- Case where $2 + m = 0$, so $m = -2$
    have hm : m = -2 := by linarith
    have hn : n = 3 := by
      rw [hm] at h1
      nlinarith
    rw [hm, hn]
    norm_num
  · -- Case where $n - 1 = 0$, so $n = 1$
    have hn : n = 1 := by linarith
    have hm : m = -6 := by
      rw [hn] at h1
      nlinarith
    rw [hm, hn] at h2
    norm_num at h2
    all_goals linarith