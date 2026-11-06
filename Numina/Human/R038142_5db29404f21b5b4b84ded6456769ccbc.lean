import Mathlib

/- A circle is centered at $(5,15)$ and has a radius of $\sqrt{130}$ units. Point $Q = (x,y)$ is on the circle, has integer coordinates, and the value of the $x$-coordinate is twice the value of the $y$-coordinate. What is the maximum possible value for $x$? -/
theorem algebra_22195 (x y : ℤ) (h : (x - 5) ^ 2 + (y - 15) ^ 2 = 130) (h' : x = 2 * y) :
    x ≤ 12 := by
        -- 将x = 2y代入圆的方程
        rw [h'] at h
        -- 化简代数式
        ring_nf at h
        -- 将方程化简为(y - 6)(y - 4) = 0
        replace h : (y - 6) * (y - 4) = 0:= by linarith
        -- 根据乘积为0，得到y = 6或y = 4
        have h1 : y - 6 = 0 ∨ y - 4 = 0:= Int.mul_eq_zero.mp h
        rcases h1 with h1 | h1
        . -- 第一种情况：y = 6
            replace h1 : y = 6 := by linarith
            -- 将y = 6代入x = 2y
            rw [h1] at h'
            norm_num at h'
            linarith
        . -- 第二种情况：y = 4
            replace h1 : y = 4 := by linarith
            -- 将y = 4代入x = 2y
            rw [h1] at h'
            norm_num at h'
            linarith
