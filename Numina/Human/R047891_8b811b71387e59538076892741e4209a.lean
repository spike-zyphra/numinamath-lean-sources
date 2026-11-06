import Mathlib
open Mathlib
/-- Suppose that a parabola has vertex $\left(\frac{1}{4},-\frac{9}{8}\right)$ and equation $y = ax^2 + bx + c$, where $a > 0$ and $a + b + c$ is an integer. The minimum possible value of $a$ can be written in the form $\frac{p}{q}$, where $p$ and $q$ are relatively prime positive integers. Find $p + q$. -/
theorem algebra_94859 (a b c : ℝ) :
IsLeast {a | ∃ b c : ℝ, a > 0 ∧ (∀ x, a * (x - 1/4)^2 - 9/8 = a * x^2 + b * x + c) ∧ ∃ n : ℤ, a + b + c = n} (2 / 9) := by
  -- https://artofproblemsolving.com/wiki/index.php/2011_AIME_I_Problems/Problem_6
  simp only [gt_iff_lt, one_div, inv_pow, exists_and_left, exists_eq_left, and_self_left]
  constructor
  -- provide witnesses
  · simp only [Set.mem_setOf_eq, Nat.ofNat_pos, div_pos_iff_of_pos_left, true_and]
    ring_nf
    exists (-1/9), (-10/9)
    norm_num
    constructor
    · ring_nf; simp only [implies_true]
    · exists -1; norm_num
  · simp only [mem_lowerBounds, Set.mem_setOf_eq, and_imp, forall_exists_index]
    intros a1 hx b1 c1 hy w hz
    norm_num at hy
    ring_nf at hy
    let als : Polynomial ℝ := Polynomial.C ((-9 / 8 : ℝ) + a1 * (1 / 16 : ℝ)) + Polynomial.X * Polynomial.C (a1 * (-1 / 2 : ℝ)) + Polynomial.X^2 * Polynomial.C a1
    let rew : Polynomial ℝ := Polynomial.C a1 * Polynomial.X^2 + Polynomial.X * Polynomial.C b1 + Polynomial.C c1
    -- prove the two polynomials are equal so we can extract coefficients
    have uuu := Polynomial.funext (p := als) (q := rew) (by intro x; unfold als rew; simp only [one_div,
      map_add, map_mul, Polynomial.X_pow_mul_C, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.X_mul_C]; have := hy x; ring_nf at this; linarith)
    -- extract -9 / 8 + a1 * (1 / 16) = c1
    have ui : als.coeff 0 = rew.coeff 0 := by rw [uuu]
    simp only [one_div, map_add, map_mul, Polynomial.X_pow_mul_C, Polynomial.coeff_add,
      Polynomial.coeff_C_zero, Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul,
      add_zero, Polynomial.coeff_X_pow, OfNat.zero_ne_ofNat, ↓reduceIte, mul_zero,
      Polynomial.X_mul_C, zero_add, als, rew] at ui; ring_nf at ui
    -- extract a1 * (-1 / 2) = b1
    have uy : als.coeff 1 = rew.coeff 1 := by rw [uuu]
    simp only [one_div, map_add, map_mul, Polynomial.X_pow_mul_C, Polynomial.coeff_add,
      Polynomial.coeff_C_succ, Polynomial.coeff_mul_C, zero_mul, add_zero, Polynomial.coeff_X_mul,
      Polynomial.mul_coeff_zero, Polynomial.coeff_C_zero, zero_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, OfNat.one_ne_ofNat, ↓reduceIte, mul_zero, Polynomial.X_mul_C,
      Polynomial.coeff_mul_X, als, rew] at uy
    -- This means that $\frac{9a-18}{16}\in \mathbb{Z}$
    have wl : (9 * a1 - 18) / 16 = ↑w := by linarith
    have ttt : -9/8 ≤ (↑w : ℝ) := by linarith
    have wle : -2 < w := by rify; clear * - ttt; linarith
    have wlf : -1 ≤ w := by linarith
    -- conclude
    rify at *
    linarith