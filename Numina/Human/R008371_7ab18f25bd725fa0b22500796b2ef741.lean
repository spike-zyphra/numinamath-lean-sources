import Mathlib

/- Given the function $f(x) = \begin{cases} x-3, & x\geq6 \\ f(f(x+5)), & x<6\end{cases}$, find the value of $f(5)$. -/
theorem algebra_9313 {f : ℝ → ℝ} (hf : ∀ x, x ≥ 6 → f x = x - 3)
    (hf' : ∀ x, x < 6 → f x = f (f (x + 5))) : f 5 = 4 := by
  -- f(5) = f(f(10)) = f(7) = 4
  calc f 5 = f (f 10) := by rw [hf' 5 (by norm_num)]; norm_num
         _ = f 7 := by rw [hf 10 (by norm_num)]; norm_num
         _ = 4 := by rw [hf 7 (by norm_num)]; norm_num
