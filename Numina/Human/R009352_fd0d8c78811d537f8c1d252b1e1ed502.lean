import Mathlib

/- Given the function $f(x)= \begin{cases} \sqrt{x}, & x\geqslant 4 \\ 2^{x}, & x < 4 \end{cases}$, find $f[f(2)]$ -/
theorem algebra_8979 {f : ℝ → ℝ} (hf : ∀ x, x ≥ 4 → f x = Real.sqrt x) (hf' : ∀ x, x < 4 → f x = 2 ^ x) : f (f 2) = 2 := by
  have h1: (2:ℝ) < 4 := by norm_num
  -- function f(x) splits at x=4. so to find f(f(2)), first, we should find f(2) >=4 or f(2) < 4. 
  have eq1: f 2 = 2^(2:ℝ) := hf' (2:ℝ) h1
  have h2: (2:ℝ)^(2:ℝ) ≥ 4 := by norm_num
  -- f(2)=4, so f(f(2)) = √(f(2))
  have eq2: f (f 2) = Real.sqrt ((2:ℝ)^(2:ℝ)) := by
    rw [eq1]
    apply hf ((2:ℝ)^(2:ℝ)) h2
  rw [eq2]
  simp