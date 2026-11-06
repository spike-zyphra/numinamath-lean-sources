import Mathlib

/- Let $x, y, z$ be positive real numbers. Prove that:
$$
\frac{x+2 y}{z+2 x+3 y}+\frac{y+2 z}{x+2 y+3 z}+\frac{z+2 x}{y+2 z+3 x} \leq \frac{3}{2}
$$ -/
theorem inequalities_605774
    (x y z : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z) :
    (x + 2 * y) / (z + 2 * x + 3 * y) +
    (y + 2 * z) / (x + 2 * y + 3 * z) +
    (z + 2 * x) / (y + 2 * z + 3 * x) ≤ 3 / 2 := by

  -- Because the inequality is homogeneous, we can take $x+y+z=1$.
  wlog h_sumxyz : x + y + z = 1
  . convert this (x / (x + y + z)) (y / (x + y + z)) (z / (x + y + z)) ?_ ?_ ?_ ?_ using 1
    any_goals positivity
    any_goals field_simp

  -- Denote $x+2 y=a, y+2 z=b, z+2 x=c$.
  let a := x + 2 * y
  let b := y + 2 * z
  let c := z + 2 * x

  -- Hence, $a+b+c=3(x+y+z)=3$.
  have h_sumabc : a + b + c = 3 := by
    dsimp [a, b, c]
    linarith

  -- We have $(k-1)^{2} \geq 0 \Leftrightarrow(k+1)^{2} \geq 4 k \Leftrightarrow \frac{k+1}{4} \geq \frac{k}{k+1}$ for all $k>0$.
  have r1 {k : ℝ} : 0 < k → k / (k + 1) ≤ (k + 1) / 4 := by
    intro h_kpos

    -- $(k+1)^{2} \geq 4 k$
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mp
    simp_rw [div_inv_eq_mul, ← pow_two]

    -- (k-1)^{2} \geq 0
    apply sub_nonneg.mp
    rw [show (k + 1) ^ 2 - k * 4 = (k - 1) ^ 2 by ring]
    positivity

  -- Hence $\sum_{\text {cyc }} \frac{x+2 y}{z+2 x+3 y}=\sum \frac{a}{1+a} \leq \sum \frac{a+1}{4}=\frac{a+b+c+3}{4}=\frac{3}{2}$.
  calc
    -- $=\sum \frac{a}{1+a}$
    _ = a / (1 + a) + b / (1 + b) + c / (1 + c) := by
      simp only [a, b, c, ← h_sumxyz]
      ring
    -- $\leq \sum \frac{a+1}{4}$
    _ ≤ (a + 1) / 4 + (b + 1) / 4 + (c + 1) / 4 := by
      have h1 := r1 (show 0 < a by positivity)
      have h2 := r1 (show 0 < b by positivity)
      have h3 := r1 (show 0 < c by positivity)
      linear_combination h1 + h2 + h3
    -- $=\frac{a+b+c+3}{4}$
    _ = (a + b + c + 3) / 4 := by
      ring_nf
    -- $=\frac{3}{2}$
    _ = 3 / 2 := by
      norm_num [h_sumabc]
