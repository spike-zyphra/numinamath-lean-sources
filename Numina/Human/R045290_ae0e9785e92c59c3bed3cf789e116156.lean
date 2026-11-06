import Mathlib

/- 1. Let $x, y, z$ satisfy:

$$

\left\{\begin{array}{l}
\log _{2}\left(x y z-3+\log _{5} x\right)=5, \\
\log _{3}\left(x y z-3+\log _{5} y\right)=4, \\
\log _{4}\left(x y z-3+\log _{5} z\right)=4 .
\end{array}\right.

$$


Then $\log _{5} x y z=$ $\qquad$ -/
theorem algebra_253479 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz₁: 0 < x*y*z-3 + Real.logb 5 x) (hxyz₂: 0 < x*y*z-3 + Real.logb 5 y) (hxyz₃: 0 < x*y*z-3 + Real.logb 5 z)
    (h1 : Real.logb 2 (x * y * z - 3 + Real.logb 5 x) = 5) (h2 : Real.logb 3 (x * y * z - 3 + Real.logb 5 y) = 4)
    (h3 : Real.logb 4 (x * y * z - 3 + Real.logb 5 z) = 4) :
    Real.logb 5 (x * y * z) = 3 := by
    -- first take out all the logs from the 3 equations
    have h1 := (Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (hxyz₁)).mp h1
    have h2 := (Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (hxyz₂)).mp h2
    have h3 := (Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (hxyz₃)).mp h3
    -- adding the 3 equation gives 3xyz = log_5(xyz) = 378
    have h : 3 * x * y * z + (Real.logb 5 x + Real.logb 5 y + Real.logb 5 z) = 378 := by linarith
    rw [← Real.logb_mul (by positivity) (by positivity)] at h
    rw [← Real.logb_mul (by positivity) (by positivity)] at h
    -- define the function f(x) = 3x + log_5(x)
    let f (a: ℝ) : ℝ := 3*a + Real.logb 5 a
    -- last equation states f(xyz) = 378
    have h : f (x*y*z) = 378 := by
      dsimp [f]
      rw [← (show 3*x*y*z = 3*(x*y*z) by ring_nf)]
      assumption
    -- while f(125) = 378 also
    have h' : f (125) = 378 := by
      dsimp [f]
      nth_rw 2 [(show 125 = (5:ℝ)^(3:ℝ) by norm_num)]
      rw [Real.logb_rpow (by norm_num) (by norm_num)]
      norm_num
    -- we'll prove f is strictly monotone on (0, ∞) as it is sum of monotone 3x and strictly monotone log_5
    have hmono₁ := strictMono_mul_left_of_pos (show (3:ℝ) > 0 by norm_num)
    have hmono₁ := StrictMono.strictMonoOn hmono₁ <| Set.Ioi 0
    have hmono₁ := StrictMonoOn.monotoneOn hmono₁
    have hmono₂ := Real.strictMonoOn_logb (show 1 < 5 by norm_num)
    have hmono := MonotoneOn.add_strictMono hmono₁ hmono₂
    -- hence it's also injective on (0, ∞)
    have hinj := StrictMonoOn.injOn hmono
    -- thereform xyz = 125, now plug in and prove
    have : x * y * z = 125 := by
      apply hinj
      . dsimp [Set.Ioi]
        positivity
      . dsimp [Set.Ioi]
        norm_num
      . change f (x*y*z) = f 125
        rw [h, h']
    rw [this]
    rw [(show (125:ℝ) = 5^(3:ℝ) by norm_num)]
    rw [Real.logb_rpow (by norm_num) (by norm_num)]