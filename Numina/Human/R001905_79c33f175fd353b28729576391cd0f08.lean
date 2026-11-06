import Mathlib

open Real Set

/- (a) Prove that for all $a, b, c, d \in \mathbb{R}$ with $a + b + c + d = 0$,
\[
\max(a, b) + \max(a, c) + \max(a, d) + \max(b, c) + \max(b, d) + \max(c, d) \geqslant 0.
\]
(b) Find the largest non-negative integer $k$ such that it is possible to replace $k$ of the six maxima in this inequality by minima in such a way that the inequality still holds for all $a, b, c, d \in \mathbb{R}$ with $a + b + c + d = 0$. -/
theorem inequalities_43840 (a b c d : ℝ) (h : a + b + c + d = 0) :
    max a b + max a c + max a d + max b c + max b d + max c d ≥ 0 := by 
  cases' max_cases a b with h₁ h₁ <;> cases' max_cases a c with h₂ h₂ <;> cases' max_cases a d with h₃ h₃ <;>
    cases' max_cases b c with h₄ h₄ <;> cases' max_cases b d with h₅ h₅ <;> cases' max_cases c d with h₆ h₆ <;>
      linarith