import Mathlib

/-The quantity $\sqrt{45} - 2\sqrt{5} + \frac{\sqrt{360}}{\sqrt{2}}$ can be expressed as $\sqrt{N}$, where $N$ is an integer. Find $N$.-/
theorem algebra_10643 {N : ℤ} (h : N = (√45 - 2 * √5 + √360 / √2)^2) : N = 245 := by
  -- We find the prime factorizations of $45$ and $360$: $45 = 3^2 \cdot 5$ and $360 = 2^3 \cdot 3^2 \cdot 5$. Hence, $$\sqrt{45} = \sqrt{3^2 \cdot 5} = 3\sqrt{5}$$
  have c1 : √45 = 3 * √5 := by
    rw [show (45 : ℝ) = 3^2 * 5 by linarith, Real.sqrt_mul]
    congr
    refine Real.sqrt_sq (by linarith)
    linarith
  --  \begin{align*}
  -- \sqrt{360} &= \sqrt{2^3 \cdot 3^2 \cdot 5}\\
  -- &= \sqrt{(2 \cdot 3)^2} \cdot \sqrt{2 \cdot 5} = 6 \sqrt{2 \cdot 5}.
  -- \end{align*}
  have c2 : √360 / √2 = 6 * √5 := by
    field_simp
    rw [mul_assoc, ←Real.sqrt_mul, show (360 : ℝ) = 6^2 * 10 by linarith, Real.sqrt_mul]
    congr
    exact Real.sqrt_sq (by linarith)
    linarith
    linarith
    linarith
  -- Returning to the given expression,  \begin{align*}
  -- 3\sqrt{5} - 2\sqrt{5} + \frac{6 \sqrt{2} \cdot \sqrt{5}}{\sqrt{2}} &= 3\sqrt{5} - 2\sqrt{5} + 6\sqrt{5}\\
  -- &= 7\sqrt{5} = \sqrt{7^2 \cdot 5} = \sqrt{245}.
  -- \end{align*}Thus, $N = \boxed{245}$.
  rw [c1, c2] at h
  ring_nf at h
  simp [Real.sq_sqrt] at h
  norm_cast at h
