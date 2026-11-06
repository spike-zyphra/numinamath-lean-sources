import Mathlib

/- Given an even function $f(x)$ defined on $\mathbb{R}$ such that $f(x) = -f(x+2)$, and when $x \in (2, 3)$, $f(x) = 3 - x$. Find the value of $f(7.5)$. -/
theorem algebra_9042 {f : ℝ → ℝ} (h₀ : ∀ x, f (-x) = f x)
    (h₁ : ∀ x, f x = -f (x + 2)) (h₂ : ∀ x ∈ Set.Ioo 2 3, f x = 3 - x) :
    f 7.5 = -0.5 := by
  -- f(7.5) = f(-7.5) = -f(-5.5) = f(-3.5) = -f(-1.5) = f(0.5) = -f(2.5) = -0.5
  calc f 7.5 = f (-7.5) := by rw [h₀]
           _ = -f (-5.5) := by rw [h₁]; norm_num
           _ = f (-3.5) := by rw [h₁]; norm_num
           _ = -f (-1.5) := by rw [h₁]; norm_num
           _ = f 0.5 := by rw [h₁]; norm_num
           _ = -f 2.5 := by rw [h₁]; norm_num
           _ = -0.5 := by rw [h₂ 2.5 ⟨by norm_num, by norm_num⟩]; norm_num
