import Mathlib

/-$f(x)$ is a monic polynomial such that $f(0)=4$ and $f(1)=10$. If $f(x)$ has degree $2$, what is $f(x)$? Express your answer in the form $ax^2+bx+c$, where $a$, $b$, and $c$ are real numbers.-/
theorem algebra_10998 {f : ℝ → ℝ} (hf : ∃ b c, f = fun x => x ^ 2 + b * x + c)
  (hf0 : f 0 = 4) (hf1 : f 1 = 10) : f = fun x => x ^ 2 + 5 * x + 4 := by
    obtain ⟨b, c, h⟩ := hf
    -- Since $f(x)$ has degree $2$, we know it is of the form $ax^2+bx+c$. A monic polynomial is one whose leading coefficient is $1$.
    simp [h] at hf0 hf1
    -- so $a=1$. Since $f(0)=4$, we know $1(0)^2+b(0)+c=4$, so $c=4$. Since $f(1)=10$, we know $1(1)^2+b(1)+4=10$, so $b+5=10$ and $b=5$. 
    simp [hf0] at hf1
    have b5 : b = 5 := by linarith
    simp [hf0, b5] at h
    -- Thus $f(x)=\boxed{x^2+5x+4}$.
    exact h
