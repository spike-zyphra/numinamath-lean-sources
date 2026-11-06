import Mathlib
/- The real function $f$ has the property that, whenever $a, b, n$ are positive integers such that $a+b=2^{n}$, the equation $f(a)+f(b)=n^{2}$ holds. What is $f(2002)$ ? -/
theorem algebra_611055 (f : ℝ → ℝ) (hf : ∀ a b n : ℕ, a > 0 → b > 0 → n > 0 → a + b = 2 ^ n → f a + f b = n ^ 2) : f 2002 = 96:= by
  -- Apply the hypothesis with a=2002, b=46, n=11 (since 2002 + 46 = 2^11)
  have h1:= hf 2002 46 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  -- Apply the hypothesis with a=46, b=18, n=6 (since 46 + 18 = 2^6)
  have h2:= hf 46 18 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  -- Apply the hypothesis with a=18, b=14, n=5 (since 18 + 14 = 2^5)
  have h3:= hf 18 14 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  -- Apply the hypothesis with a=14, b=2, n=4 (since 14 + 2 = 2^4)
  have h4:= hf 14 2 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  -- Apply the hypothesis with a=2, b=2, n=2 (since 2 + 2 = 2^2)
  have h5:= hf 2 2 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  -- Simplify the equations
  simp at h1 h2 h3 h4 h5
  -- Normalize numerical expressions in all equations
  norm_num at h1 h2 h3 h4 h5
  -- Use linear arithmetic to prove f(2002) = 96 from the system of equations
  linarith
