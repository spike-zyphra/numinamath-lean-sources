import Mathlib
open Polynomial

/- Suppose that $p(x)$ is a polynomial and that $p(x) - p'(x) = x ^ 2 + 2 x + 1$. Compute $p(5)$. -/
theorem algebra_608633 {p : ℝ[X]} (h : p - derivative p = X ^ 2 + 2 * X + 1) :
    p.eval 5 = 50 := by

  -- let `q` be the right-hand-side of the equation.
  let q : ℝ[X] := X ^ 2 + 2 * X + 1
  rw [show X ^ 2 + 2 * X + 1 = q by rfl] at h

  -- Obviously, `p ≠ 0`, otherwise we have `0 = X ^ 2 + 2 * X + 1`.
  have hp_ne_zero: p ≠ 0 := by
    by_contra! hp
    unfold q at h
    simp [hp] at h
    have := congrArg (eval 1) h
    simp at this
    norm_num at this

  -- Observe that $p(x)$ and $q(x)$ must be quadratic.
  have hq_degree : q.degree = 2 := by
    unfold q
    rw [show (X: ℝ[X]) ^ 2 = 1 * X ^ 2 by ring]
    apply degree_quadratic
    simp

  have hp_degree : p.degree = 2 := by
    rw [← hq_degree, ← h]
    rw [show p - derivative p = p + (- derivative p) by ring]
    apply Eq.symm (degree_add_eq_left_of_degree_lt _)
    simp
    exact degree_derivative_lt hp_ne_zero

  -- Let $p(x)=a x^{2}+b x+c$. 
  let a := p.coeff 2
  let b := p.coeff 1
  let c := p.coeff 0
  have hp : p = (C a) * (X: ℝ[X]) ^ 2 + (C b) * (X: ℝ[X]) + C c := by
    ext n
    cases le_or_gt n 2 with
    | inl h1 =>
      cases le_or_gt n 1 with
      | inl h11 =>
        cases le_or_gt n 0 with
        | inl h111 =>
          have : n = 0 := by linarith
          simp [this]
        | inr h112 =>
          have : n = 1 := by linarith
          simp [this]
      | inr h12 =>
        have : n = 2 := by linarith
        simp [this]
    | inr h2 =>
      have : p.degree < n := by rw [hp_degree]; norm_cast
      have := coeff_eq_zero_of_degree_lt this
      rw [this]
      have : ((C a) * (X: ℝ[X]) ^ 2 + (C b) * (X: ℝ[X]) + C c).degree = 2 := by
        apply degree_quadratic
        unfold a
        exact coeff_ne_zero_of_eq_degree hp_degree
      have : ((C a) * (X: ℝ[X]) ^ 2 + (C b) * (X: ℝ[X]) + C c).degree < n := by
        rw [this]; norm_cast
      rw [coeff_eq_zero_of_degree_lt this]

  -- Such that $p'(x)=2 a x + b$. 
  have hp_der : derivative p = 2 * (C a) * (X: ℝ[X]) + C b := by
    rw [hp]
    have : C a * C 2 = 2 * C a := by exact CommMonoid.mul_comm (C a) (C 2)
    simp; ring_nf
    rw [this]
    ring

  have hp_der_1 := coeff_derivative p 1
  have hp_der_0 := coeff_derivative p 0
  norm_num at hp_der_1
  norm_num at hp_der_0

  -- Comparing coefficients gives $a=1, b-2 a=2$, and $c-b=1$.
  have ha : a = 1 := by
    have := congrArg (fun po => coeff po 2) h
    unfold q at this
    rw [hp_der, hp] at this
    simp at this
    rw [show coeff (1: ℝ[X]) 2 = 0 by apply coeff_C_succ] at this
    rw [show coeff (X: ℝ[X]) 2 = 0 by apply coeff_X_of_ne_one (by linarith)] at this
    simp at this
    exact this

  have heq1 : b - a * 2 = 2 := by
    have := congrArg (fun po => coeff po 1) h
    simp at this
    unfold q at this
    rw [hp_der_1] at this
    simp at this
    rw [show coeff (1: ℝ[X]) 1 = 0 by apply coeff_C_succ] at this
    simp at this
    exact this

  rw [ha] at heq1
  simp at heq1
  have hb: b = 4 := by linarith

  have heq0 : c - b = 1 := by
    have := congrArg (fun po => coeff po 0) h
    simp at this
    unfold q at this
    rw [hp_der_0] at this
    simp at this
    exact this

  have hc: c = 5 := by
    rw [hb] at heq0
    linarith
  
  -- As a result, $b=4, c=5, p(x)=x^{2}+4 x+5$ and $p(5)=25+20+5=50$.
  rw [hp, ha, hb, hc]
  norm_num
