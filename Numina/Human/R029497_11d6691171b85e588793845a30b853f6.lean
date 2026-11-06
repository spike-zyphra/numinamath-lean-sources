import Mathlib

open Real

/- Let $x,$ $y,$ and $z$ be positive real numbers.  Find the minimum value of
\[\frac{\sqrt{x^2 + y^2} + \sqrt{x^2 + z^2} + \sqrt{y^2 + z^2}}{x + y + z}.\] -/
theorem algebra_21454 :
    IsLeast {((sqrt (x ^ 2 + y ^ 2) + sqrt (x ^ 2 + z ^ 2) + sqrt (y ^ 2 + z ^ 2)) / (x + y + z)) |
      (x : ℝ) (hx : 0 < x) (y : ℝ) (hy : 0 < y) (z : ℝ) (hz : 0 < z)} (sqrt 2) := by
        constructor <;>
        simp [lowerBounds]
        . use 1
          constructor
          . linarith
          . use 1
            constructor
            . linarith
            . use 1
              constructor
              . linarith
              . simp
                field_simp
                calc _ = √2 + √2 + √2:= by ring_nf
                    _ = _:= by ring_nf
        . intro a x hx y hy z hz h
          -- 引理h1：对于任意正实数a和b，有： √(a² + b²) ≥ (a + b)/√2 这是证明的关键不等式
          have h1 (a b : ℝ) (ha : a > 0) (hb : b > 0) : √(a ^ 2 + b ^ 2) ≥ (a + b) / √2 := by
            calc _ = √(2 * (a ^ 2 + b ^ 2) / 2):= by ring_nf
                -- 使用平方差公式：a² + b² = ((a+b)² + (a-b)²)/2
                _ = √(((a + b) ^ 2 + (a - b) ^ 2) / 2):= by ring_nf
                --由于(a-b)²≥0，所以可以去掉这一项得到更小的值
                _ ≥ √(((a + b) ^ 2 + 0) / 2):= by
                  have _ : (a - b) ^ 2 ≥ 0:= by exact sq_nonneg (a - b)
                  apply sqrt_le_sqrt (show ((a + b) ^ 2 + 0) / 2 ≤ ((a + b) ^ 2 + (a - b) ^ 2) / 2 by linarith)
                _ = √(((a + b) ^ 2) / 2):= by ring_nf
                _ = √((a + b) ^ 2) / √2:= by rw [Real.sqrt_div (show 0 ≤ (a + b) ^ 2 by exact sq_nonneg (a + b)) 2]
                _ = (a + b) / √2:= by rw[Real.sqrt_sq (show 0 ≤ (a + b) by linarith)]
          -- 将h1应用于三对数(x,y), (x,z), (y,z)
          have h2 := h1
          have h3 := h1
          specialize h1 x y hx hy
          specialize h2 x z hx hz
          specialize h3 y z hy hz
          -- 证明关键不等式：√(x²+y²) + √(x²+z²) + √(y²+z²) ≥ √2(x+y+z)
          have h4 : √(x ^ 2 + y ^ 2) + √(x ^ 2 + z ^ 2) + √(y ^ 2 + z ^ 2) ≥ √2 * (x + y + z):= by
            calc _ ≥ (x + y) / √2 + (x + z) / √2 + (y + z) / √2:= by linarith
                _ =  (x + y + x + z + y + z) / √2:= by ring_nf
                _ = (x + y + z) * (2 / √2):= by ring_nf
                _ = (x + y + z) * (√(2 ^ 2) / √2):= by rw[Real.sqrt_sq (show 0 ≤ 2 by linarith)]
                _ = (x + y + z) * √(2 ^ 2 / 2):= by rw[Real.sqrt_div (show 0 ≤ 2 ^ 2 by exact sq_nonneg 2) 2]
                _ = √2 * (x + y + z):= by ring_nf
          -- 证明分母为正
          have hpos: 1 / (x + y + z) > 0:= by
            have _ : x + y + z > 0:= by linarith
            exact div_pos (show 0 < 1 by linarith) (show 0 < x + y + z by linarith)
          -- 最终证明a ≥ √2，即√2是最小值
          have h5 : a ≥ √2:= by
            calc _ = (√(x ^ 2 + y ^ 2) + √(x ^ 2 + z ^ 2) + √(y ^ 2 + z ^ 2)) / (x + y + z):= by rw[←h]
                _ ≥ √2 * (x + y + z) / (x + y + z):= by
                  calc _ = (√(x ^ 2 + y ^ 2) + √(x ^ 2 + z ^ 2) + √(y ^ 2 + z ^ 2)) * (1 / (x + y + z)):= by field_simp
                        _ ≥ √2 * (x + y + z) * (1 / (x + y + z)):= mul_le_mul_of_nonneg_right h4 (show 0 ≤ 1 / (x + y + z) by linarith)
                        _ = _:= by field_simp
                _ = √2 * 1:= by field_simp
                _ = √2:= by ring_nf
          linarith
