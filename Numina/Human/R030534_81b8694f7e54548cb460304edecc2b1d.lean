import Mathlib

open Real

/-- If $f(x) = ax + b$ and $f^{-1}(x) = bx + a$ with $a$ and $b$ real, what is the value of
$a + b$? -/
theorem algebra_96851 {a b : ℝ} (f : ℝ → ℝ) (hf : f = fun x => a * x + b)
    (hinv : ∀ x, f (b * x + a) = x) : a + b = -2 := by

  -- Since $f(f^{-1}(x))=x$, it follows that $a(bx+a)+b=x$
  have habx (x : ℝ) : a * (b * x + a) + b = x := by
    calc _ = f (b * x + a) := by rw [hf]
         _ = x := by rw [hinv]

  -- which implies $abx + a^2 +b = x$.
  replace habx (x : ℝ) : a * b * x + a^2 + b = x := by nth_rewrite 2 [←habx x]; ring

  -- Substituting $x=0$ gives $a^2+b=0$.
  have hab1 : a^2 + b = 0 := by linarith only [habx 0]

  -- Then $b = -a^2$.
  have hb : b = -a^2 := by linarith only [hab1]

  -- Substituting $x=1$ gives $ab + a^2 + b = 1$.
  have hab2 : a*b + (a^2 + b) = 1 := by linarith only [habx 1]
  -- Therefore, $ab=1$.
  replace hab2 : a * b = 1 := by linarith only [hab2, hab1]

  -- Substituting $b=-a^2$ gives $-a^3=1$.
  have ha : a^3 = -1 := by rw [hb] at hab2; linarith only [hab2]
  -- Therefore, $a=-1$.
  replace ha : a = -1 := (pow_eq_neg_one_iff.mp ha).1

  -- Substituting $a=-1$ into $ab = 1$ gives $b=-1$.
  replace hb : b = -1 := by rw [hb, ha]; norm_num

  -- Therefore, $a+b=-2$.
  rw [ha, hb]
  norm_num