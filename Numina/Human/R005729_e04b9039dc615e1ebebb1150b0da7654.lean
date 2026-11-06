import Mathlib

/- Let $r_{1}, r_{2}, r_{3}, r_{4}$ be the four roots of the polynomial $x^{4}-4 x^{3}+8 x^{2}-7 x+3$. Find the value of

$$
\frac{r_{1}^{2}}{r_{2}^{2}+r_{3}^{2}+r_{4}^{2}}+\frac{r_{2}^{2}}{r_{1}^{2}+r_{3}^{2}+r_{4}^{2}}+\frac{r_{3}^{2}}{r_{1}^{2}+r_{2}^{2}+r_{4}^{2}}+\frac{r_{4}^{2}}{r_{1}^{2}+r_{2}^{2}+r_{3}^{2}}
$$-/
theorem algebra_609610 (r : Fin 4 → ℝ) (hx : ((Polynomial.X - Polynomial.C (r 0)) * (Polynomial.X - Polynomial.C (r 1)) * (Polynomial.X - Polynomial.C (r 2)) * (Polynomial.X - Polynomial.C (r 3)) : Polynomial ℝ) = Polynomial.X ^ 4 - 4 * Polynomial.X ^ 3 + 8 * Polynomial.X ^ 2 - 7 * Polynomial.X + Polynomial.C 3) :
    r 0 ^ 2 / (r 1 ^ 2 + r 2 ^ 2 + r 3 ^ 2) + r 1 ^ 2 / (r 0 ^ 2 + r 2 ^ 2 + r 3 ^ 2) + r 2 ^ 2 / (r 0 ^ 2 + r 1 ^ 2 + r 3 ^ 2) + r 3 ^ 2 / (r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2) = -4 := by
  -- Compare coefficients to show some equalities.
  -- First show that r 0 * r 1 * r 2 * r 3 = 3.
  have h₀ : r 0 * r 1 * r 2 * r 3 = 3 := by
    replace hx := congr_arg (Polynomial.eval (0 : ℝ) ·) hx
    simp at hx
    exact hx
  -- Then show that r 0 + r 1 + r 2 + r 3 = 4.
  have h₁ : r 0 + r 1 + r 2 + r 3 = 4 := by
    ring_nf at hx
    rw [<-Polynomial.coeff_inj] at hx
    replace hx := congr_arg (· 3) hx
    simp at hx
    repeat rw [mul_assoc] at hx
    repeat rw [Polynomial.coeff_C_mul] at hx
    rw [Polynomial.coeff_X_pow, Polynomial.coeff_X_of_ne_one (by norm_num)] at hx
    simp at hx
    linarith only [hx]
  -- Then show that r 0 * r 1 + r 0 * r 2 + r 0 * r 3 + r 1 * r 2 + r 1 * r 3 + r 2 * r 3 = 8.
  have h₂ : r 0 * r 1 + r 0 * r 2 + r 0 * r 3 + r 1 * r 2 + r 1 * r 3 + r 2 * r 3 = 8 := by
    ring_nf at hx
    rw [<-Polynomial.coeff_inj] at hx
    replace hx := congr_arg (· 2) hx
    simp at hx
    repeat rw [mul_assoc] at hx
    repeat rw [Polynomial.coeff_C_mul] at hx
    rw [Polynomial.coeff_X_pow_self, Polynomial.coeff_X_of_ne_one (by norm_num)] at hx
    linarith only [hx]
  -- First show that r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 + r 3 ^ 2 = 0.
  have h₃ : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 + r 3 ^ 2 = 0 := by
    -- We have r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 + r 3 ^ 2 = (r 0 + r 1 + r 2 + r 3) ^ 2 - 2 * (r 0 * r 1 + r 0 * r 2 + r 0 * r 3 + r 1 * r 2 + r 1 * r 3 + r 2 * r 3).
    replace h₁ := congr_arg (· ^ 2) h₁
    simp at h₁
    linarith
  -- Add 4 to both sides at the goal.
  suffices (r 0 ^ 2 / (r 1 ^ 2 + r 2 ^ 2 + r 3 ^ 2) + 1) + (r 1 ^ 2 / (r 0 ^ 2 + r 2 ^ 2 + r 3 ^ 2) + 1) + (r 2 ^ 2 / (r 0 ^ 2 + r 1 ^ 2 + r 3 ^ 2) + 1) + (r 3 ^ 2 / (r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2) + 1) = 0 by
    linarith only [this]
  repeat rw [div_add_one]
  -- Substitute r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 + r 3 ^ 2 = 0.
  suffices (r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 + r 3 ^ 2) / (r 1 ^ 2 + r 2 ^ 2 + r 3 ^ 2) + (r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 + r 3 ^ 2) / (r 0 ^ 2 + r 2 ^ 2 + r 3 ^ 2) + (r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 + r 3 ^ 2) / (r 0 ^ 2 + r 1 ^ 2 + r 3 ^ 2) + (r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 + r 3 ^ 2) / (r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2) = 0 by
    ring_nf at this ⊢
    exact this
  simp [h₃]
  -- Prove the remaining goals concerning the nonzeroness of the denominators.
  . by_contra!
    have : r 3 ^ 2 = 0 := by
      linarith
    simp at this
    simp [this] at h₀
  . by_contra!
    have : r 2 ^ 2 = 0 := by
      linarith
    simp at this
    simp [this] at h₀
  . by_contra!
    have : r 1 ^ 2 = 0 := by
      linarith
    simp at this
    simp [this] at h₀
  . by_contra!
    have : r 0 ^ 2 = 0 := by
      linarith
    simp at this
    simp [this] at h₀
