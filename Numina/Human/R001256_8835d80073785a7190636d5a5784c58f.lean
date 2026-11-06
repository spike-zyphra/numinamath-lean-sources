import Mathlib

/- Let \[f(x) = \left\{
\begin{array}{cl}
2x + 1 & \text{if } x \le 3, \\
8 - 4x & \text{if } x > 3.
\end{array}
\right.\]Find the sum of all values of $x$ such that $f(x) = 0.$ -/
theorem algebra_22229 (f : ℝ → ℝ)
    (h₀ : ∀ x, x ≤ 3 → f x = 2 * x + 1)
    (h₁ : ∀ x, x > 3 → f x = 8 - 4 * x) :
    ∑ᶠ x ∈ {x | f x = 0}, x = -1 / 2 := by 
  have h₂ : ∀ x, f x = 0 → x = -1 / 2 := by
    intro x hx
    by_cases hx' : x ≤ 3
    · rw [h₀ x hx'] at hx
      linarith
    · push_neg at hx'
      rw [h₁ x hx'] at hx
      linarith
  have h₃ : f (-1 / 2) = 0 := by
    rw [h₀ _ (by norm_num)]
    norm_num
  have h₄ : ∀ x, f x = 0 → x = -1 / 2 := by
    intro x hx
    by_cases hx' : x ≤ 3
    · rw [h₀ x hx'] at hx
      linarith
    · push_neg at hx'
      rw [h₁ x hx'] at hx
      linarith
  have h₅ : ∑ᶠ x ∈ {x | f x = 0}, x = -1 / 2 := by
    have h₆ : {x | f x = 0} = {-1 / 2} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · apply h₄
      · intro hx
        rw [hx]
        exact h₃
    rw [h₆]
    simp
  exact h₅