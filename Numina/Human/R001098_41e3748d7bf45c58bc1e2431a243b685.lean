import Mathlib

/- Let $x=\frac{7}{8}$ and $y=-\frac{2}{9}$.  If $x\cdot z = y$, then what is $z$? -/
theorem algebra_20430 {x y z : ℚ} (hx : x = 7 / 8) (hy : y = -2 / 9) (hxy : x * z = y) :
    z = -16 / 63 := by
    -- 在等式 hxy 中代入 x 和 y 的值
    rw [hx, hy] at hxy
    -- 使用线性算术求解器自动计算结果
    linarith
