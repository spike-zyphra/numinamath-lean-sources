import Mathlib

open Real

/- Soit $n$ un entier strictement positif et $x \geqslant n$ un réel. Montrer que $x+\frac{n}{x} \geqslant n+1$ et donner les cas d'égalité. -/
theorem inequalities_607364 (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : n ≤ x) :
    x + n / x ≥ n + 1 ∧ (x + n / x = n + 1 ↔ x = n) := by
    have hn: n ≥ 1 := by linarith;
    have hcast: 1 ≤ (x:ℝ) := by
      have _: 1 ≤ (n:ℝ) := by norm_cast;
      linarith;

    -- Step 1: expand the "or" in the goal and tackle them one at a time.
    constructor
    
    -- Step 2: Times x to both side of ineq and proof the ineq case
    have h1: (x + n/x)*x ≥ (n+1)*x := by
      rw [add_mul, add_mul]
      field_simp
      ring_nf
      have ht1: - ↑n * x - x + ↑n + x ^ 2 ≥ 0 := by
        calc - ↑n * x - x + ↑n + x ^ 2 = (x - 1) * (x - ↑n) := by ring_nf;
        _ ≥ 0 := by
          have hxp : x - 1 ≥ 0 := by linarith;
          have hxn : x - ↑n ≥ 0 := by linarith;
          exact mul_nonneg hxp hxn;
      linarith
    have h1': x*(n+1) ≤ x*(x + n/x) := by linarith
    apply le_of_mul_le_mul_left h1' (by positivity)


    -- Step 3: Solve the equality case.

    -- Step 3.1 Right arrow
    constructor
    intro eq;field_simp at eq
    have ht1: (x - 1) * (x - ↑n) = 0 := by linarith
    rcases mul_eq_zero.mp ht1 with ht1l | ht1r
    have xe1: x=1 := by linarith
    rw [xe1] at hx
    have hn': 1 ≤ (n:ℝ) := by norm_cast;
    linarith;

    linarith;
    -- Step 3.2: Solve the converse.
    intro cxn;rw[cxn];field_simp


      
    