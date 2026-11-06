import Mathlib

/- Suppose that $g(x)=f^{-1}(x)$. If $g(-15)=0$, $g(0)=3$, $g(3)=9$ and $g(9)=20$, what is $f(f(9))$? -/
theorem algebra_21563 {f g : ℝ → ℝ} (hf : Function.LeftInverse g f)
    (hg : Function.RightInverse g f) (h₁ : g (-15) = 0) (h₂ : g 0 = 3) (h₃ : g 3 = 9)
    (h₄ : g 9 = 20) : f (f 9) = 0 := by 
  have h₅ := hf 9
  have h₆ := hg 9
  have h₇ := hf 0
  have h₈ := hg 0
  have h₉ := hf 3
  have h₁₀ := hg 3
  simp_all