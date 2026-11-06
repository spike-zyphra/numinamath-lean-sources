import Mathlib
/-The solutions to the equation $(x+1)(x+2) = x+3$ can be written in the form $m+\sqrt n$ and $m-\sqrt n$, where $m$ and $n$ are integers. What is $m+n$?-/
theorem algebra_19259 (m n : ℤ) (hx : {x | (x + 1) * (x + 2) = x + 3} = {m + √n, m - √n})(hn : 0 ≤ n):
  m + n = 1 := by
    --First, find the roots of the equation
    ring_nf at hx
    have heq : {x | 2 + x * 3 + x ^ 2 = 3 + x} = {-1+√2,-1-√2}  := by
      ext x
      constructor
      .
        --Forward proof
        intro h
        -- we expand the left side of our equation to get $$x^2+3x+2 = x+3.$$
        simp; simp at h
        --Then we subtract $x+3$ from both sides to get a quadratic equation in standard form: $$x^2+2x-1 = 0.$$
        have e :=  congrArg ( fun (t) => (t) - 3 - x ) h; simp at e; rw [show 2 + x * 3 + x ^ 2 - 3 - x  = 1 * (x * x) + 2 * x + (-1) by ring_nf] at e
        --This doesn't factor in an obvious way, so we apply the quadratic formula, which gives solutions of $$x = \frac{-(2) \pm\sqrt{(2)^2 - 4(1)(-1)}}{2(1)} = \frac{-2\pm\sqrt{8}}{2}.$$
        have hd : discrim (1:ℝ) (2) (-1) = 2*√2 * (2*√2) := by
          rw [discrim]; ring_nf
          simp; ring_nf
        have ha : (1 : ℝ) ≠ 0 := by simp
        --We can simplify this, dividing $2$ out of the numerator and denominator to obtain $$x = -1\pm\sqrt{2}.$$
        rw [quadratic_eq_zero_iff  ha hd x] at e; ring_nf at e
        exact e
      .
        --reverse proof
        intro h
        simp at h
        --Substitute two into the equation
        cases h with
        | inl h =>
          rw [h] ; norm_num; ring_nf; simp ; ring
        | inr h =>
          rw [h] ; norm_num; ring_nf; simp ; ring
    --Discuss two different cases corresponding to m+√ n and m - √ n, respectively
    rw [heq,Set.pair_eq_pair_iff] at hx
    cases hx with
    | inl h =>
        cases h with
        | intro left right =>
          --Add the two equations together to find m
          have e :=  congrArg ( fun (t) => ((t) + (- 1 - √2)) / 2 ) left; beta_reduce at e ; nth_rewrite 2 [right] at e;simp at e; ring_nf at e
          --substitute them to find n
          rw [e] at left; simp at left; rw [Real.sqrt_eq_iff_eq_sq,Real.sq_sqrt] at left; norm_cast at e; simp at e; symm at e; norm_cast at left; symm at left
          --Thus, the integers $m$ and $n$ referred to in the problem are $m=-1$, $n=2$, and their sum is $-1+2=\boxed{1}$.
          rw [e,left]; ring_nf
          --Because the root ，n is greater than or equal to 0, verify the inequality
          norm_cast
          linarith
          simp only [Real.sqrt_nonneg]
    | inr h =>
        cases h with
        | intro left right =>
          --Add the two equations together to find m
          have e :=  congrArg ( fun (t) => ((t) + (- 1 - √2)) / 2 ) left; beta_reduce at e ; nth_rewrite 2 [right] at e;simp at e; ring_nf at e
          --substitute them to find n
          rw [← e] at right
          --Because the root ，n is greater than or equal to 0, the inequality does not hold
          have e2 :=  congrArg ( fun (t) => (t) + 1) right;ring_nf at e2
          have hsq : 0 ≤ √↑n := by apply Real.sqrt_nonneg
          have hsq2 : 0 < √2 := by simp
          rw [← e2] at hsq; linarith

