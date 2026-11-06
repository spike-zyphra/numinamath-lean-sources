import Mathlib

theorem algebra_183319 : ¬∃ p q : Polynomial ℝ, ∀ x y : ℝ, x^200 * y^200 + 1 = p.eval x * q.eval y := by
  intro h
  rcases h with ⟨p, q, h_eq⟩
  have eq1 := h_eq 1 1
  have eq2 := h_eq 0 0
  have eq3 := h_eq (0 : ℝ) 1
  have eq4 := h_eq 1 (0 : ℝ)
  -- convert to direct equation expressions
  -- eq3: p(0)*q(1) = 1
  -- eq4: p(1)*q(0) = 1
  -- eq1: p(1)*q(1) = 2
  -- eq2: p(0)*q(0) = 1
  norm_num at eq1 eq2 eq3 eq4
  -- solving the system of equations
  -- From eq3 and eq4:
  -- From eq1:
  -- p(1)/p(0) = 2
  -- From eq3 and eq4:
  -- q0 = 1/p1 and q1 = 1/p0
  -- However, nlinarith in Lean would solve it.
  nlinarith [sq_nonneg (p.eval 0), sq_nonneg (p.eval 1), sq_nonneg (q.eval 0), sq_nonneg (q.eval 1)]