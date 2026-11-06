import Mathlib

/-
Problem

Given that the point $(4,7)$ is on the graph of $y=f(x)$, there is one point that must be on the graph of $2y=3f(4x)+5$. What is the sum of the coordinates of that point?
-/
theorem algebra_1436 (hf : condf = fun (f : ℝ → ℝ) => f 4 = 7) (h1 : ∀ f, condf f → 2 * y = 3 * f (4 * x) + 5) : x + y = 14 := by 
  -- we only need to prove x = 1 ∧ y = 13.
  suffices x = 1 ∧ y = 13 by norm_num [this]
  have xeq1 : x = 1 := by 
    by_contra!
    let f1 := fun (m : ℝ) => ite (m = (4 *x)) (0 : ℝ) 7 
    let f2 := fun (m : ℝ) => ite (m = (4 *x)) (1 : ℝ) 7
    have condf1 : condf f1 := by norm_num [f1, hf, this]
    have condf2 : condf f2 := by norm_num [f2, hf, this]
    have h₁ := h1 f1 condf1 
    have h₂ := h1 f2 condf2 
    simp [f1] at h₁
    simp [f2] at h₂
    linarith 
  let f3 := fun (_ : ℝ) => (7 : ℝ)
  have condf3 : condf f3 := by simp [f3, hf]
  have := h1 f3 condf3 
  norm_num [f3] at this
  exact ⟨xeq1, by linarith⟩ 
