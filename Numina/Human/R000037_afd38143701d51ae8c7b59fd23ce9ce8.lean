import Mathlib

/-- Define sol as the set of ordered pairs $(x,y)$ such that $x^{2}+xy+y^{2} \leq 2007$-/
def sol_4069 := ((Int.range (-100) 100).product (Int.range (-100) 100)).filter
  fun (a, b) => a ^ 2 + a * b + b ^ 2 ≤ 2007

-- check that $N = 7229$
#eval sol_4069.length

/-- Let $\( N \)$ be the number of ordered pairs $\((x, y)\)$ of integers such that
\[
x^{2}+xy+y^{2} \leq 2007.
\]
Prove that $\( N \)$ is odd. Prove that $\( N \)$ is not divisible by 3. -/
theorem number_theory_4069 : Odd 7229 ∧ ¬ 3 ∣ 7229 := ⟨by decide, by decide⟩
