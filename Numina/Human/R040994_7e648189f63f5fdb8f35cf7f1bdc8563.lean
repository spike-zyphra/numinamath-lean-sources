import Mathlib
open Mathlib

/--
Suppose that $f(x+3)=3x^2 + 7x + 4$ and $f(x)=ax^2 + bx + c$. What is $a+b+c$?
$\textbf{(A)}\ -1 \qquad \textbf{(B)}\ 0 \qquad \textbf{(C)}\ 1 \qquad \textbf{(D)}\ 2 \qquad \textbf{(E)}\ 3$
-/
lemma algebra_1207 (f : ℝ → ℝ) (a b c : ℝ) (h1 : ∀ x, f (x + 3) = 3 * x^2 + 7*x + 4) (h2 : ∀ x, f x = a * x^2 + b * x + c) : a + b + c = 2 := by
  have stp : ∀ (x : ℝ), f x = 3 * (x - 3)^2 + 7 * (x - 3) + 4 := by
    intro x
    have := h1 (x - 3)
    rw [(by ring : x - 3 + 3 = x)] at this
    exact this
  -- f x = 10 - x * 11 + x ^ 2 * 3
  ring_nf at stp
  let akjdl : Polynomial ℝ := Polynomial.C a * Polynomial.X^2 + Polynomial.C b * Polynomial.X + Polynomial.C c
  let adkd : Polynomial ℝ := Polynomial.C 3 * Polynomial.X^2 + Polynomial.C (-11) * Polynomial.X + Polynomial.C 10
  -- Prove two polynomials are equal
  have ald : akjdl = adkd := by
    apply Polynomial.funext
    intro r
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, map_neg, neg_mul, Polynomial.eval_neg, akjdl, adkd]
    have ad := h2 r
    have dk := stp r
    rw [dk] at ad
    rw [← ad]
    ring
  -- a = 3
  have ww : akjdl.coeff 2 = adkd.coeff 2 := by rw [ald]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ↓reduceIte,
    mul_one, Polynomial.coeff_mul_X, Polynomial.coeff_C_succ, add_zero, map_neg, neg_mul,
    Polynomial.coeff_neg, neg_zero, akjdl, adkd] at ww
  -- b = -11
  have dd : akjdl.coeff 1 = adkd.coeff 1 := by rw [ald]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    OfNat.one_ne_ofNat, ↓reduceIte, mul_zero, Polynomial.coeff_mul_X, Polynomial.coeff_C_zero,
    zero_add, Polynomial.coeff_C_succ, add_zero, map_neg, neg_mul, Polynomial.coeff_neg, akjdl,
    adkd] at dd
  -- c = 10
  have ss : akjdl.coeff 0 = adkd.coeff 0 := by rw [ald]
  simp only [Polynomial.coeff_add, Polynomial.mul_coeff_zero, Polynomial.coeff_C_zero,
    Polynomial.coeff_X_pow, OfNat.zero_ne_ofNat, ↓reduceIte, mul_zero, Polynomial.coeff_X_zero,
    add_zero, zero_add, map_neg, neg_mul, Polynomial.coeff_neg, neg_zero, akjdl, adkd] at ss
  rw [ww, dd, ss]
  -- 3 + -11 + 10 = 2
  norm_num