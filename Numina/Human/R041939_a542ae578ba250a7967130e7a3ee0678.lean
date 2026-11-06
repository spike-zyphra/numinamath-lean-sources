import Mathlib
/-What is the sum of the positive integers that are solutions of $-3n +3 >-11?$-/
 theorem algebra_20497 :
     { n |  n > (0 : ℤ) ∧ (-3)* n + 3 > -11} = {1,2,3,4} ∧  ∑ n in {1,2,3,4} , n = 10 := by
    --Adding $3n+11$ to both sides, we get $$-3n+3+3n+11 > -11+3n+11,$$ which simplifies to $$14 > 3n.$$ Dividing both sides by $3$ gives $$4\frac 23 > n.
    --$$ The integer solutions are $n=1,2,3,4$, and their sum is $\boxed{10}$.
    simp
    --Prove that both sides of the set are equal
    ext n
    constructor
    .
      intro h
      simp at h; simp
      omega
    .
      intro h
      simp at h; simp
      omega
