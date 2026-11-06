import Mathlib
/-Let $f(x) = x + 2$ and $g(x) = 1/f(x)$. What is $g(f(-3))$?-/
theorem algebra_516 {f g : ℝ → ℝ} (hf : f = fun x => x + 2) (hg : g = fun x => 1 / f x) :
    g (f (-3)) = 1 := by
    --计算f -3 和 f -1 的值
    have h1 : f (-3) = -1 := by
      simp [hf];norm_num
    have h2 : f (-1) = 1 := by
      simp [hf];norm_num
    --f -3带入目标中
    simp[h1,hg]
    exact h2
