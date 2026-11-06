import Mathlib

/- Let $p$ and $q$ be the two distinct solutions to the equation $$\frac{4x-12}{x^2+2x-15}=x+2.$$If $p > q$, what is the value of $p - q$? -/
theorem algebra_15949 {p q : ℝ} (hpq1 : p ≠ q)(hpq2: p > q)
  (h : (4 * p - 12) / (p ^ 2 + 2 * p - 15) = p + 2)
  (h' : (4 * q - 12) / (q ^ 2 + 2 * q - 15) = q + 2) :
  p - q = 5 := by
  -- first, simplify the equation
  have h1(x:ℝ)(hx: x ≠ 3): (4*x - 12) / (x^2+2*x-15) = 4/(x+5) := by
    have hh1: 4*x - 12 = (x-3)*4 := by ring
    -- notice that x^2+2x-15 = (x-3)(x+5)
    have hh2: (x^2+2*x-15) = (x-3)*(x+5) := by ring
    -- thus we can cancel common factor (x-3)
    have hh3: x -3 ≠ 0 := by
      exact sub_ne_zero_of_ne hx
    rw [hh2, hh1]
    exact mul_div_mul_left 4 (x + 5) hh3
  -- now the equation turns to 4/(x+5) = x+2, or 4 = (x+5)(x+2). simplify, it is (x+6)(x+1) = 0
  have h2(x:ℝ): (4*x-12)/(x^2+2*x-15) = x+2 → (x+6)*(x+1) = 0 := by
    intro heq
    have hx1: x ≠ 3 := by
      by_contra! hc; rw [hc] at heq; norm_num at heq
    have hx2: x ≠ -5 := by
      by_contra! hc; rw [hc] at heq; norm_num at heq
    rw [h1 x hx1] at heq
    have hh1: x+5 ≠ 0 := by
      have: x+5 = x- -5 := by ring
      rw [this]; apply sub_ne_zero_of_ne hx2
    have hh2: 4 = (x+2)*(x+5) := by
      have: 4 = 4/(x+5) * (x+5) := by
        symm; exact div_mul_cancel₀ 4 hh1
      rw [this, heq]
    have hh3: (x+6)*(x+1) = (x+5)*(x+2)-4 := by ring
    rw [hh3, hh2]; ring
  -- so two solutions are -6 and -1
  have h3(x:ℝ): (4*x-12)/(x^2+2*x-15) = x+2 → x=-6 ∨ x=-1 := by
    intro heq
    rcases (mul_eq_zero.mp (h2 x heq)) with hl | hr
    · left; linarith [hl]
    · right; linarith [hr]
  -- p > q, so p is -1, q is -6, and p-q = 5
  rcases (h3 p h) with pn6 | pn1
  · rcases (h3 q h') with qq | qq
    <;> rw [pn6, qq] at hpq2 <;> norm_num at hpq2
  · rcases (h3 q h') with qn6 | qn1
    · rw [pn1, qn6]; norm_num
    · rw [pn1, qn1] at hpq2; simp at hpq2