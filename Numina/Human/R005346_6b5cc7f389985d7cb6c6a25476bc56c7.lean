import Mathlib

/- Let $x, y$ be positive reals such that $x+y=2$. Prove that

$$
x^{3} y^{3}\left(x^{3}+y^{3}\right) \leq 2
$$-/
theorem inequalities_607799 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 2) :
    x^3 * y^3 * (x^3 + y^3) ≤ 2 := by
  --   We have from the AM-GM inequality, that
  -- $$
  -- x y \leq\left(\frac{x+y}{2}\right)^{2}=1
  -- $$
  -- Thus we obtain $0 < x y \leq 1$.
  have key1 : x * y ≤ 1 := calc
    _ ≤ ((x + y) / 2) ^ 2 := by
      rw [← mul_le_mul_iff_of_pos_right (by norm_num : 0 < (4 : ℝ)), ← sub_nonneg]
      calc
        _ ≤ (x - y) ^ 2 := by positivity
        _ = _ := by ring
    _ = _ := by norm_num [hxy]
  --   We write
  -- $$
  -- \begin{aligned}
  -- x^{3} y^{3}\left(x^{3}+y^{3}\right) & =(x y)^{3}(x+y)\left(x^{2}-x y+y^{2}\right) \\
  -- & =2(x y)^{3}\left((x+y)^{2}-3 x y\right) \\
  -- & =2(x y)^{3}(4-3 x y)
  -- \end{aligned}
  -- $$
  have key2 : x ^ 3 + y ^ 3 = 2 * (4 - 3 * (x * y)) := calc
    _ = (x + y) * (x ^ 2 - x * y + y ^ 2) := by ring
    _ = 2 * (x ^ 2 - x * y + y ^ 2) := by rw [hxy]
    _ = 2 * ((x + y) ^ 2 - 3 * x * y) := by ring
    _ = _ := by rw [hxy]; ring
  -- Thus we need to prove that
  -- $$
  -- (x y)^{3}(4-3 x y) \leq 1
  -- $$
  rw [key2, ← mul_pow, ← sub_nonneg]
  -- Putting $z=x y$, this inequality reduces to
  -- $$
  -- z^{3}(4-3 z) \leq 1
  -- $$
  set z := x * y
  -- for $0 < z \leq 1$. We can prove this in different ways.
  -- We can put the inequality in the form
  -- $$
  -- 3 z^{4}-4 z^{3}+1 \geq 0
  -- $$
  -- Here the expression in the LHS factors to
  -- $(z-1)^{2}\left(3 z^{2}+2 z+1\right)$ and
  convert_to 0 ≤ 2 * (z - 1) ^ 2 * (3 * z ^ 2 + 2 * z + 1)
  . ring
  suffices 0 ≤ 3 * z ^ 2 + 2 * z + 1 by positivity
  -- $\left(3 z^{2}+2 z+1\right)$ is positive since its discriminant $D=-8<0$.
  nlinarith
