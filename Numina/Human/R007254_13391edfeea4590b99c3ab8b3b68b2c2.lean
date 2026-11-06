import Mathlib

/- What value of $x$ will give the minimum value for $9x^2 + 18x + 7$? -/
theorem algebra_22032 (f : ℝ → ℝ) (hf : f = fun x => 9 * x ^ 2 + 18 * x + 7) :
    IsMinOn f (Set.univ : Set ℝ) (-1) := by
        -- 展开 IsMinOn 的定义
        simp [IsMinOn, IsMinFilter]
        intro x
        -- 代入 f 的表达式
        simp [hf]
        -- 由平方非负性
        have h1 : (3 * x + 3) ^ 2 ≥ 0:= by exact sq_nonneg (3 * x + 3)
        -- 线性组合得到所需不等式
        linarith
