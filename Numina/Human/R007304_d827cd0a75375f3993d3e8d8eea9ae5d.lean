import Mathlib

/- Two weeks ago, Alice came home from vacation and noticed that a bean plant was growing in her garden. Today, the stalk is $452$ centimeters tall, and Alice observed that its height increases by $5\%$ every day.  How tall was the plant $2$ weeks ago when she first noticed it growing? Express your answer as a decimal to the nearest tenth. -/
theorem algebra_22224 (a : ℝ) (h : a * (1 + 5 / 100) ^ 14 = 452) :
    (round (a * 10) : ℝ) / 10 = 228.3 := by
    -- 在假设h中进行数值计算
    norm_num at h
    -- 将h重写为a的显式表达式
    replace h : a = 452 / (3243919932521508681 / 1638400000000000000) := by linarith
    -- 继续进行数值计算
    norm_num at h
    -- 将a替换为计算得到的值
    subst a
    -- 使用round_eq引理
    rw [round_eq]
    -- 完成最终的数值计算
    norm_num
