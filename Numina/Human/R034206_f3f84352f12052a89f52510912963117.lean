import Mathlib
open Polynomial

/- Find all solutions to $x^4 + 2x^3 + 2x^2 + 2x + 1 = 0 (including non-real solutions)$ -/
theorem algebra_608603 :
    {x : ℂ | x ^ 4 + 2 * x ^ 3 + 2 * x ^ 2 + 2 * x + 1 = 0}
    =  {-1, - Complex.I, Complex.I} := by
  let p1 : Polynomial ℂ := X^4 + 2*X^3 + 2*X^2 + 2*X + 1
  let p2 : Polynomial ℂ := (X - C (- 1)) * (X - C (- 1)) * (X - C Complex.I) * (X - (- C Complex.I))
  
  -- We can factor the polynomial as $(x+1)^{2}\left(x^{2}+1\right)$.
  have hfac1 : p1 = p2 := by ring_nf; rw [← C_pow, Complex.I_sq]; simp; ring

  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    have : eval x p1 = 0 := by unfold p1; simp; exact h
    have : eval x p2 = 0 := by rw [← hfac1]; exact this
    unfold p2 at this
    -- So, the solutions are $x + 1 = 0$, $x + i = 0$ or $x - i = 0$,
    simp at this
    obtain hx1 | hx2 := this
    obtain hx1_1 | hx1_2 := hx1
    -- which means that $x$ is $-1$ or $\pm i$
    left; exact eq_neg_of_add_eq_zero_left hx1_1
    right; right; rw [sub_eq_zero] at hx1_2; exact hx1_2
    right; left; exact eq_neg_of_add_eq_zero_left hx2
  · intro hx
    -- It's easy to check that these values do satisfy the equation.
    obtain hx1 | hx2 := hx
    rw [hx1]; ring_nf
    obtain hx2_1 | hx2_2 := hx2
    rw [hx2_1]; ring_nf;
    rw [show Complex.I ^ 3 = Complex.I ^ 2 * Complex.I by ring,
        show Complex.I ^ 4 = Complex.I ^ 2 * Complex.I ^ 2 by ring,
        Complex.I_sq]
    ring
    rw [hx2_2]; ring_nf;
    rw [show Complex.I ^ 3 = Complex.I ^ 2 * Complex.I by ring,
        show Complex.I ^ 4 = Complex.I ^ 2 * Complex.I ^ 2 by ring,
        Complex.I_sq]
    ring
