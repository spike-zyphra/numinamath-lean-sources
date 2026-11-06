import Mathlib

/-Let $a, b, c, d$ be real numbers so that $c, d$ are not both 0 .
Define the function
$$
m(x)=\frac{a x+b}{c x+d}
$$
on all real numbers $x$ except possibly $-d / c$, in the event that $c \neq 0$.
Suppose that the equation $x=m(m(x))$ has at least one solution that is not a solution of $x=m(x)$.
Find all possible values of $a+d$. Prove that your answer is correct.-/
theorem algebra_611550 :
    { t | ∃ a b c d : ℝ, ∃ m : ℝ → ℝ, ∃ x : ℝ, (c ≠ 0 ∨ d ≠ 0) ∧ t = a + d ∧
    (m = fun x ↦ (a * x + b) / (c * x + d)) ∧ x = m (m x) ∧ x ≠ m x ∧ c * x + d ≠ 0 ∧ c * m x + d ≠ 0} =
    { 0 } := by
  ext t
  constructor
  --  First, we show $a+d=0$ if exists
  · intro ht
    obtain ⟨a, b, c, d, m, x, hcd, rfl, hm, hx1, hx2, hx3, hx4⟩ := ht
    simp only [Set.mem_singleton_iff]
    field_simp [hm] at hx4
    field_simp [hm, hx4] at hx1 hx2
    rw [← sub_eq_zero] at hx1
    -- By direct computation,
    -- $m(m(x))=x \Rightarrow (a+d)(cx² + (-a+d)x-b)=0$
    replace hx1 : (a + d) * (c * x ^ 2 + (- a + d) * x - b) = 0 := by
      rw [← hx1]
      ring
    -- $m(x)\neq 0 \Rightarrow cx² + (-a+d)x-b \neq 0$
    have hx5 : c * x ^ 2 + (- a + d) * x - b ≠ 0 := by
      intro hx5
      absurd hx2
      rw [← sub_eq_zero]
      rw [← hx5]
      ring
    -- Hence, $a + d = 0$
    simp [mul_eq_zero, hx5] at hx1
    exact hx1
  -- Second, $a+d=0$ is possible.
  · intro ht
    simp at ht
    -- Take $a=0, b = c = 0, d = -1, m (x) = - x, x = 1$
    use 1, 0, 0, -1, fun x ↦ - x, 1
    -- Easy to verify that it satisfies condition.
    simp [ht]
    constructor
    · ext
      ring
    · norm_num

