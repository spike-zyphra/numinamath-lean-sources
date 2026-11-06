import Mathlib

/- Given that $f(3)=5$ and $f(3x)=f(x)+2$ for all $x > 0$, find $f^{-1}(11)$. -/
theorem algebra_20693 {f : ℝ → ℝ} (h3 : f 3 = 5) (hf : ∀ x > 0, f (3 * x) = f x + 2)(hfinv: Function.LeftInverse (f.invFun) f):
    f.invFun 11 = 81 := by
  -- apply f(3x) = fx+2 repeatedly
  have hh1: f 9 = 7 := by
    have: (9:ℝ) = 3*3 := by norm_num
    rw [this, hf 3 (by norm_num), h3]; ring
  have hh2: f 27 = 9 := by
    have: (27:ℝ) = 3*9 := by norm_num
    rw [this, hf 9 (by norm_num), hh1]; ring
  have hh3: f 81 = 11 := by
    have: (81:ℝ) = 3*27 := by norm_num
    rw [this, hf 27 (by norm_num), hh2]; ring
  -- f(81)=11, so 81 is in the preimage set of 11.
  rw [← hh3]
  exact hfinv 81