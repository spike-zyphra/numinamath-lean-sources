import Mathlib

/- 19. A5 (JAP) ${ }^{\text {IMO6 }}$ Find all the functions $f: \mathbb{R} \rightarrow \mathbb{R}$ that satisfy  $$ f(x-f(y))=f(f(y))+x f(y)+f(x)-1 $$  for all $x, y \in \mathbb{R}$. -/
theorem algebra_24915 {f : ℝ → ℝ} (h : ∀ x y, f (x - f y) = f (f y) + x * f y + f x - 1) :
    ∀ x, f x = 1 - x ^ 2 / 2 := by
  -- Plugging in x = y = 0.
  have h₀ := h 0 0
  -- Let c = f(0) and simplify h₀
  let c := f 0
  simp [show f 0 = c by simp [c]] at h₀
  -- Show that c ≠ 0.
  have h₁ : c ≠ 0 := by
    -- Assume c = 0, then contradiction.
    by_contra! h₁
    rw [h₁] at h₀
    simp at h₀
    linarith only [h₀]
  -- Show that for each y ∈ ℝ, f(f(y)) = (c + 1) / 2 - (f(x))² / 2.
  have h₂ (y : ℝ) : f (f y) = (c + 1) / 2 - (f y) ^ 2 / 2 := by
    -- Substitute x = f(y) into the original equation.
    specialize h (f y) y
    simp [show f 0 = c by simp [c]] at h
    linarith only [h]
  -- Show that each y ∈ ℝ can be represented as f(x₁) - f(x₂) for some x₁, x₂ ∈ ℝ.
  have h₃ (y : ℝ) : ∃ x₁ x₂ : ℝ, y = f x₁ - f x₂ := by
    -- Substitute y = 0 into original equation.
    have h₃ (x : ℝ) := h x 0
    simp [show f 0 = c by simp [c]] at h₃
    -- Solve for x₁ and x₂ by setting y = f(c) + cx - 1.
    let x := (y + 1 - f c) / c
    use (x - c), x
    -- Show that y = f(c) + cx - 1.
    have : y = f c + c * x - 1 := by
      simp [x]
      rw [mul_div_cancel₀ _ h₁]
      simp
    rw [this]
    linarith only [h₃ x]
  -- Substitute x = f(x₁) and y = x₂ into the original equation.
  have h₄ (y : ℝ) : f y = c - y ^ 2 / 2 := by
    -- Use h₃ to find x₁ and x₂ such that y = f(x₁) - f(x₂).
    obtain ⟨x₁, x₂, rfl⟩ := h₃ y
    -- Substitute x = f(x₁) and y = x₂ into the original equation to simplify the goal.
    rw [h (f x₁) x₂]
    -- Use h₂ to arrive at the goal.
    linarith only [h₂ x₁, h₂ x₂]
  -- Combine h₄ and h₂.
  have h₅ (y : ℝ) : (c + 1) / 2 - f y ^ 2 / 2 = c - f y ^ 2 / 2 := by
    linarith only [h₂ y, h₄ (f y)]
  -- Show that c = 1.
  have h₆ : c = 1 := by
    specialize h₅ 0
    simp at h₅
    linarith only [h₅]
  -- Show that f(x) = 1 - x² / 2 for all x ∈ ℝ.
  intro x
  rw [h₄ x, h₆]
