import Mathlib

/- 25. [13] Let $x, y, z$ be real numbers satisfying

$$

\begin{aligned}
2 x+y+4 x y+6 x z & =-6 \\
y+2 z+2 x y+6 y z & =4 \\
x-z+2 x z-4 y z & =-3
\end{aligned}

$$


Find $x^{2}+y^{2}+z^{2}$. -/
theorem algebra_178600 {x y z : ℝ}
    (h1 : 2 * x + y + 4 * x * y + 6 * x * z = -6)
    (h2 : y + 2 * z + 2 * x * y + 6 * y * z = 4)
    (h3 : x - z + 2 * x * z - 4 * y * z = -3) :
    x ^ 2 + y ^ 2 + z ^ 2 = 29 := by
    --Multiply by 1/2 the first equation both sides
    have hk1 := congrFun (congrArg HMul.hMul h1) (1/2)
    --Multiply by -1/2 the second equation both sides
    have hk2 := congrFun (congrArg HMul.hMul h2) (-1/2)
    --Multiply by -1 the third equation both sides
    have hk3 := congrFun (congrArg HMul.hMul h3) (-1)
    --Add the three equation obtained this way
    have eq: x * y + x * z + y * z = -2 := by linarith
    --Multiply by -1 the first equation both sides
    have hk1' := congrFun (congrArg HMul.hMul h1) (-1)
    --Multiply by 2 the second equation both sides
    have hk2' := congrFun (congrArg HMul.hMul h2) (2)
    --Multiply by 3 the thrid equation both sides
    have hk3' := congrFun (congrArg HMul.hMul h3) (3)
    --Add the three equation obtained this way
    have eq': x + y + z = 5 := by linarith
    --Square both sides of eq'
    have eq'' := congrFun (congrArg HPow.hPow eq') 2
    --Resolve (a+b+c)^2
    repeat rw [add_sq] at eq''
    --Find the result by linear arithmetic
    linarith