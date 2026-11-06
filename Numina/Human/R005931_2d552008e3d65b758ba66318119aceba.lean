import Mathlib
/- Let

$$
f(x)=||\cdots||| | x|-1|-2|-3|-\cdots|-10|
$$

Compute $f(1)+f(2)+\cdots+f(54)+f(55)$. -/
theorem algebra_610780 (f : ℝ → ℝ) (hf : f = fun x => |(|(|(|(|(|(|(|(|(|(|x| - 1)| - 2)| - 3)| - 4)| - 5)| - 6)| - 7)| - 8)| - 9)| - 10)|) : ∑ i in Finset.range 55, f (i + 1) = 285:= by
  -- apply the definition of f
  repeat rw [Finset.sum_range_succ]
  simp [hf]
  -- use norm_num to simplify the expression
  norm_num
