import Mathlib

/-- IsLinear denote that a function is linear. -/  
def IsLinear (f : ℝ → ℝ) := ∃ a b, ∀ x, f x = a * x + b 

/-- Suppose that $f(x)$ is a linear function satisfying the equation $f(x) = 4f^{-1}(x) + 6$. Given that $f(1) = 4$, find $f(2)$.-/
theorem algebra_4082 {f g : ℝ → ℝ}
    (hf : IsLinear f) (hg : g.RightInverse f)
    (h₁ : ∀ x, f x = 4 * g x + 6) (h₂ : f 1 = 4) : f 2 = 6 := by
  obtain ⟨a, b, hf⟩ := hf
  -- the inversion function $g(x) = f^{-1}(x)$ means that $f(g(x)) = x$ for every $x$.
  change ∀ x, f (g x) = x at hg
  -- apply f at both sides of `h₁` and simplify, we get the following equation.
  have eq (x : ℝ) : a * a * x + (a * b + b) = 4 * x + (6 * a - 3 * b) := calc
    _ = f (f x) := by rw [hf, hf]; ring
    _ = f (4 * g x + 6) := by congr; exact h₁ x
    _ = 4 * f (g x) + (6 * a - 3 * b) := by rw [hf, hf]; ring
    _ = _ := by rw [hg]
  -- according to above equation, the constant term of both sides are equal. i.e. 
  -- $a * b - 6 * a + 4 * b = 0$. 
  have h₃ : a * b - 6 * a + 4 * b = 0 := by
    have := eq 0
    rw [← sub_eq_zero] at this
    refine Eq.trans ?_ this
    ring
  have h₄ : a = 2 ∨ a = -2 := by
    apply eq_or_eq_neg_of_sq_eq_sq
    have := eq 1
    linarith
  clear eq
  cases' h₄ with h₄ h₄
  · rw [h₄] at h₃; have := hf 2; linarith
  · rw [h₄] at h₃; have := hf 1; linarith
