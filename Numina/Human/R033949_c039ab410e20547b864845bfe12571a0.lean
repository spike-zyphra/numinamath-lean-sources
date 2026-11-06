import Mathlib

/- Find all real functions $f$ from $\mathbb{R} \rightarrow \mathbb{R}$ satisfying the relation

$$
f\left(x^{2}+y f(x)\right)=x f(x+y)
$$ -/
theorem algebra_607898 :
  {f : ℝ → ℝ | ∀ x y : ℝ, f (x ^ 2 + y * f x) = x * f (x + y)} = {0, id} := by
  ext f
  simp
  constructor
  -- First, we verify that the functions 0 and id satisfy the relation.
  swap
  . rintro (rfl | rfl) x y
    . simp
    . simp
      ring
  -- Now, suppose f is a function that satisfies the relation.
  . intro H
    -- Put x = 0, we get f (y * f 0) = 0 for all y.
    have h₀ (y : ℝ) : f (y * f 0) = 0 := by
      specialize H 0 y
      simp at H
      exact H
    -- We show f 0 = 0.
    have h₁ : f 0 = 0 := by
      -- If otherwise, put y = 0 in h₀ and we get a contradiction.
      by_contra! h₁
      specialize h₀ 0
      simp at h₀
      exact False.elim (h₁ h₀)
    -- Two cases:
    by_cases h₂ : ∃ x₀ ≠ 0, f x₀ = 0
    . -- Case 1: There exists x₀ ≠ 0 such that f x₀ = 0.
      rcases h₂ with ⟨x₀, hx₀, hx₀'⟩
      -- Put x = x₀, we get f (x₀ ^ 2) = x₀ * f (x₀ + y) for all y
      -- LHS is a constant, so f is the constant function 0.
      specialize H x₀
      simp [hx₀'] at H
      replace H (x : ℝ) : f x = f (x₀ ^ 2) / x₀ := by
        specialize H (x - x₀)
        simp at H
        field_simp
        linear_combination -H
      replace H (x : ℝ) : f x = 0 := by
        have h₂ := H x
        have h₃ := H 0
        linear_combination h₁ + h₂ - h₃
      exact Or.inl (funext H)
    . -- Case 2: For all x ≠ 0, f x ≠ 0.
      -- That is, f x = 0 implies x = 0.
      simp [not_imp_not] at h₂
      -- Set y = -x, we get f (x ^ 2 - x * f x) = 0.
      replace H (x : ℝ) : f (x ^ 2 - x * f x) = 0 := by
        specialize H x (-x)
        simp [h₁] at H
        ring_nf at H ⊢
        exact H
      -- Now we prove f x = x.
      right
      ext x
      simp
      specialize H x
      -- x ^ 2 - x * f x = 0 by h₂.
      apply h₂ at H
      -- If x = 0, we have f 0 = 0 by h₁.
      -- If x ≠ 0, we can cancel x on both sides.
      by_cases h : x = 0
      . simp [h, h₁]
      . replace H : x * f x = x * x := by linear_combination -H
        simp [h] at H
        exact H
