import Mathlib

/-Given the function $f(x) = x^3 + x$, where $a, b, c \in \mathbb{R}$, and $a+b>0$, $b+c>0$, $c+a>0$, then the value of $f(a) + f(b) + f(c)$ is definitely (fill in "greater" or "smaller") than zero.-/
theorem algebra_9442 {f : ℝ → ℝ} (hf : ∀ x, f x = x ^ 3 + x)
  (a b c : ℝ) (ha : a + b > 0) (hb : b + c > 0) (hc : c + a > 0) :
  f a + f b + f c > 0 := by
  simp [hf]
  -- an auxiliary lemma : for any real number $a$ and $b$, if $a < b$, then $a^3 < b^3$.
  have aux : ∀ a b : ℝ, a < b → a^3 < b^3 := by
    intro x y hxy
    exact Odd.strictMono_pow (by decide) hxy
  have : 0 < a^3 + b^3 + c^3 := by
    -- Because $a + b > 0$, i.e. $a > -b$, we get $a^3 > -b^3$, i.e. $0 < a^3 + b^3$.
    have ha3 : 0 < a^3 + b^3 := by
      have := aux (-b) a (by linarith)
      linarith
    -- Because $b + c > 0$, i.e. $b > -c$, we get $b^3 > -c^3$, i.e. $0 < b^3 + c^3$.
    have hb3 : 0 < b^3 + c^3 := by
      have := aux (-c) b (by linarith)
      linarith
    -- Because $c + a > 0$, i.e. $c > -a$, we get $c^3 > -a^3$, i.e. $0 < c^3 + a^3$.
    have hc3 : 0 < c^3 + a^3 := by
      have := aux (-a) c (by linarith)
      linarith
    linarith
  -- We have $a + b + c > 0$ and $a^3 + b^3 + c^3 > 0$, so `f a + f b + f c > 0`.
  linarith
