import Mathlib

/- 15. (9) Find $q$, for which $x^{2}+x+q=0$ has two distinct real roots satisfying the relation $x_{1}^{4}+2 x_{1} x_{2}^{2}-x_{2}=19$. -/

-- prove vieta's sum formula for x1 ≠ x2 root in quadratic of our problem, easier then using polynomial
lemma l_quadratic_vieta_sum (x1 x2 : ℝ) (h : x1 ≠ x2) (h1 : x1^2 + x1 + q = 0)
    (h2 : x2^2 + x2 + q = 0) : x1 + x2 = -1 := by
  have h3 : (x1 - x2) * (x1 + x2 + 1) = 0 := by linarith
  have h4 : x1 - x2 ≠ 0 := by
    apply sub_ne_zero_of_ne h
  simp [h4] at h3
  linarith

-- prove vieta's product formula for x1 ≠ x2 root in quadratic of our problem, easier then using polynomial
lemma l_quadratic_vieta_prod (x1 x2 : ℝ) (h : x1 ≠ x2) (h1 : x1^2 + x1 + q = 0)
    (h2 : x2^2 + x2 + q = 0) : x1 * x2 = q := by
  have h3 : x1 + x2 = -1 := l_quadratic_vieta_sum x1 x2 h h1 h2
  have h4 : x1 * (x1 + 1) + q = 0 := by linarith
  have h5 : x1 * (-x2) + q = 0 := by
    convert h4 using 3
    linarith
  linarith

theorem algebra_187138 {q x1 x2 : ℝ} (h : x1 ≠ x2) (h1 : x1^2 + x1 + q = 0) (h2 : x2^2 + x2 + q = 0) :
    x1^4 + 2 * x1 * x2^2 - x2 = 19 ↔ q = -3 := by
  -- first convert equation by using the fact that x^2 = - x - q
  have h3 : x1^2 = - x1 - q := by linarith
  have h4 : x1^4 = (- x1 - q)^2 := by rw [← h3]; ring
  have h5 : x2^2 = - x2 - q := by linarith
  rw [h4, h5]
  ring_nf
  rw [h3]
  ring_nf
  -- now we can plug in product and sum formiula
  have h6 : -x1 - x1 * x2 * 2 + (-x2 - q) + q ^ 2 = 1 - q * 3 + q^2 := by
    have := l_quadratic_vieta_prod x1 x2 h h1 h2
    have := l_quadratic_vieta_sum x1 x2 h h1 h2
    linarith
  rw [h6]
  -- factorize which implies q = -3 or q = 6
  convert_to (q - - 3) * (q - 6) = 0 ↔ q = -3
  . constructor <;> rintro h <;> linarith
  simp [-sub_neg_eq_add]
  rw [sub_eq_zero, sub_eq_zero]
  -- we'll prove q = 6 implies q = -3, i.e. we'll prove contradiction
  simp
  rintro h7
  exfalso
  rw [h7] at h1
  -- to prove that we'll show there is no root
  replace h1 : 1 * (x1 * x1) + 1 * x1 + 6 = 0 := by linarith
  suffices 1 * (x1 * x1) + 1 * x1 + 6 ≠ 0 by contradiction
  -- this will be proved by discriminant not being a square
  apply quadratic_ne_zero_of_discrim_ne_sq
  rintro s
  simp [discrim]
  -- the discriminant can't be square as it's negative
  have : 0 ≤ s^2 := by positivity
  linarith