import Mathlib

open Real Set
open scoped BigOperators

/- For a real number $x,$ let
\[f(x) = \max \{|x + 15|, |x + 12|, |x + 8|, |x - 1|, |x - 3|, |x - 19|\}.\]Find the minimum value of $f(x).$ -/
theorem algebra_21612 :
  -- 证明 17 是集合的最小元素
  -- 这个集合包含了函数 f(x) 的所有可能值
  IsLeast {x | ∃ t : ℝ, x = max (max (max (max (abs (t + 15)) (abs (t + 12))) (abs (t + 8))) (abs (t - 1))) (max (abs (t - 3)) (abs (t - 19)))} 17 := by
    constructor <;>
    simp [lowerBounds]
    -- 第一部分：证明 17 属于这个集合
    .
      use 2  -- 使用 t = 2 作为例子
      norm_num
    -- 第二部分：证明 17 是下界
    .
      intro a
      -- 关键引理：对任意实数 a，|a + 15| 和 |a - 19| 中至少有一个大于等于 17
      have h : 17 ≤ |a + 15| ∨ 17 ≤ |a - 19|:= by
        by_contra H  -- 反证法
        simp at H
        rcases H with ⟨h1, h2⟩
        -- 利用三角不等式：|a + 15| + |a - 19| ≥ |34|
        have h3 : |a + 15| + |a - 19| ≥ 34:= by
          calc _ ≥ |a + 15 - (a - 19)|:= by exact abs_sub (a + 15) (a - 19)
               _ = |34|:= by ring_nf
               _ ≥ 34:= by exact le_abs_self 34
        linarith
      -- 根据上述引理完成证明
      rcases h with h | h
      .
        left
        left
        left
        left
        exact h
      .
        right
        right
        exact h
