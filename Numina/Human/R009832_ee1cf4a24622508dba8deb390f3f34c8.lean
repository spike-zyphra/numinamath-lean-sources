import Mathlib

/- Let $\mathbb{R}$ be the set of real numbers. Let $f: \mathbb{R} \rightarrow \mathbb{R}$ be a function such that  $$ f(x+y) f(x-y) \geqslant f(x)^{2}-f(y)^{2} $$  for every $x, y \in \mathbb{R}$. Assume that the inequality is strict for some $x_{0}, y_{0} \in \mathbb{R}$. Prove that $f(x) \geqslant 0$ for every $x \in \mathbb{R}$ or $f(x) \leqslant 0$ for every $x \in \mathbb{R}$. (Malaysia) Common remarks. We will say that $f$ has constant sign, if $f$ satisfies the conclusion of the problem. -/
theorem inequalities_607764 (f : ℝ → ℝ) (h : ∀ x y, f (x + y) * f (x - y) ≥ f x ^ 2 - f y ^ 2) (h' : ∃ x₀ y₀, f (x₀ + y₀) * f (x₀ - y₀) > f x₀ ^ 2 - f y₀ ^ 2) :
    (∀ x, f x ≥ 0) ∨ (∀ x, f x ≤ 0) := by
  -- Prove that f(s)f(t) ≥ f((s + t) / 2)² - f((s - t) / 2)² for all s, t ∈ ℝ.
  have h₀ (s t : ℝ) : f s * f t ≥ f ((s + t) / 2) ^ 2 - f ((s - t) / 2) ^ 2 := by
    -- Substitute x = (s + t) / 2 and y = (s - t) / 2 into the original equation.
    have : f ((s + t) / 2 + (s - t) / 2) * f ((s + t) / 2 - (s - t) / 2) ≥ f ((s + t) / 2) ^ 2 - f ((s - t) / 2) ^ 2 := h ((s + t) / 2) ((s - t) / 2)
    ring_nf at this ⊢
    exact this
  -- Prove that f(s)f(-t) ≥ f((s - t) / 2)² - f((s + t) / 2)² for all s, t ∈ ℝ.
  have h₁ (s t : ℝ) : f s * f (-t) ≥ f ((s - t) / 2) ^ 2 - f ((s + t) / 2) ^ 2 := by
    -- Substitute x = (s - t) / 2 and y = (s + t) / 2 into the original equation.
    have : f ((s - t) / 2 + (s + t) / 2) * f ((s - t) / 2 - (s + t) / 2) ≥ f ((s - t) / 2) ^ 2 - f ((s + t) / 2) ^ 2 := h ((s - t) / 2) ((s + t) / 2)
    ring_nf at this ⊢
    exact this
  -- Sum up the two inequalities.
  have h₂ (s t : ℝ) : f s * (f t + f (-t)) ≥ 0 := by
    linarith only [h₀ s t, h₁ s t]
  -- Consider the case when f(x₀ + y₀) * f(x₀ - y₀) > f(x₀)² - f(y₀)².
  obtain ⟨x₀, y₀, h'⟩ := h'
  -- Substitute s₀ = x₀ + y₀ and t₀ = x₀ - y₀ into the inequality.
  let s₀ := x₀ + y₀
  let t₀ := x₀ - y₀
  replace h' : f s₀ * f t₀ > f ((s₀ + t₀) / 2) ^ 2 - f ((s₀ - t₀) / 2) ^ 2 := by
    simp [s₀, t₀]
    exact h'
  -- Note that f(s₀)f(-t₀) ≥ f((s₀ - t₀) / 2)² - f((s₀ + t₀) / 2)².
  have h'' := h₁ s₀ t₀
  -- Sum up the two inequalities to get f(s₀)(f(t₀) + f(-t₀)) > 0, and hence f(t₀) + f(-t₀) ≠ 0.
  have h₃ : f s₀ * (f t₀ + f (-t₀)) ≠ 0 := by
    linarith only [h', h'']
  simp at h₃
  nth_rw 2 [<-ne_eq] at h₃
  -- Note that f(s)(f(t₀) + f(-t₀)) ≥ 0 for all s ∈ ℝ.
  replace h₂ (s : ℝ) := h₂ s t₀
  by_cases h₄ : f t₀ + f (-t₀) > 0
  . -- Consider the case when f(t₀) + f(-t₀) > 0.
    -- Note that f(s) ≥ 0 for all s ∈ ℝ.
    left
    intro s
    nlinarith [h₂ s]
  . -- Consider the case when f(t₀) + f(-t₀) < 0.
    -- Note that f(s) ≤ 0 for all s ∈ ℝ.
    right
    intro s
    replace h₄ : f t₀ + f (-t₀) < 0 := by
      simp at h₄
      apply lt_of_le_of_ne h₄ h₃.2
    nlinarith [h₂ s]