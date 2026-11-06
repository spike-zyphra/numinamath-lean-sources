import Mathlib

open Nat

/- Simplify the expression $\sqrt{7!}$, where $n!$ stands for $n\cdot(n-1)\cdot(n-2)\cdots \cdot 2\cdot 1$. -/
theorem algebra_20979 : √(7!) = 12 * √35 := by
  -- 首先将 7! 展开为具体的乘积形式
  have h1 : 7! = 7 * 6 * 5 * 4 * 3 * 2 * 1 := by rfl
  rw [h1]
  ring_nf
  calc _ = √(12 ^ 2 * 35)  := by ring_nf    -- 将表达式重写为完全平方数与其他因子的乘积形式
       _ = √(12 ^ 2) * √35 := Real.sqrt_mul' (12 ^ 2) (by linarith)    -- 使用根号乘法法则：√(a*b) = √a * √b
       _ = 12 * √35 := by rw [Real.sqrt_sq (by linarith)]    -- 化简 √(12^2) 得到 12
       _ = √35 * 12 := by ring_nf    -- 调整乘法顺序（可选步骤）