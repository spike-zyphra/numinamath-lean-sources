import Mathlib

/- The product of $3t^2+5t+a$ and $4t^2+bt-2$ is $12t^4+26t^3-8t^2-16t+6$. What is $a+b$? -/
theorem algebra_22130 {a b : ℝ} (h : ∀ t : ℝ, (3 * t ^ 2 + 5 * t + a) * (4 * t ^ 2 + b * t - 2) = 12 * t ^ 4 + 26 * t ^ 3 - 8 * t ^ 2 - 16 * t + 6) :
    a + b = -1 := by
    -- 将原假设复制一份
    have h1:= h
    -- 将 t = 0 代入第一个等式
    specialize h1 0
    -- 将 t = 1 代入第二个等式
    specialize h 1
    -- 化简两个等式
    simp at h1 h
    -- 从第一个等式得出 a = -3
    replace h1 : a = -3 := by linarith
    -- 将 a = -3 代入第二个等式
    rw [h1] at h
    -- 继续化简
    simp at h
    -- 从化简后的等式得出 b = 2
    replace h : b = 2 := by linarith
    -- 最后证明 a + b = -1
    linarith
