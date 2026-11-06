import Mathlib

theorem algebra_180704 {x y : ℝ} (hx : x^2 * (1 - 3 * Complex.I) - 10 = -y * (y - Complex.I)) :
    (x = 1 ∧ y = -3) ∨ (x = -1 ∧ y = -3) := by
  have eq1 := congr_arg Complex.re hx
  have eq2 := congr_arg Complex.im hx
  simp [pow_two, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.I_im] at eq1 eq2
  have h1 : x^2 + y^2 = 10 := by nlinarith
  have h2 : y = -3 * x^2 := by
    nlinarith
  have h3 : 9 * x^4 + x^2 - 10 = 0 := by
    nlinarith [h1, h2]
  have h4 : (x^2 - 1) * (9 * x^2 + 10) = 0 := by
    nlinarith
  cases' (mul_eq_zero.1 h4) with h5 h6
  · -- Case $x^2 - 1 = 0$, so $x^2 = 1$
    have h8 : x^2 = 1 := by
      nlinarith
    have hx1 : x = 1 ∨ x = -1 := by 
      rw [sq_eq_one_iff] at h8
      exact h8
    have hy1 : y = -3 := by
      nlinarith [h2, h8]
    cases hx1 with
    | inl hx2 =>
      left
      exact ⟨hx2, hy1⟩
    | inr hx2 =>
      right
      exact ⟨hx2, hy1⟩
  · -- Case $9x^2 + 10 = 0$
    have h7 : x^2 < 0 := by
      nlinarith
    nlinarith [sq_nonneg x]