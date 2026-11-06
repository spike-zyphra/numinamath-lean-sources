import Mathlib
set_option autoImplicit false
theorem algebra_225292:
    ∃ (f g : ℝ → ℝ),
    (∀ x : ℝ, 0 ≤ f x ∧ f x ≤ 1) ∧ (∀ x : ℝ, 0 ≤ g x ∧ g x ≤ 1) ∧
    (∃ p₁ : ℝ, p₁ > 0 ∧ ∀ x : ℝ, f (x + p₁) = f x) ∧
    (∃ p₂ : ℝ, p₂ > 0 ∧ ∀ x : ℝ, g (x + p₂) = g x) ∧
    (∃ p₃ : ℝ, p₃ > 0 ∧ ∀ x : ℝ, f (x + p₃) + g (x + p₃) = f x + g x) ∧
    ¬∃ p : ℝ, p > 0 ∧ 
      (∀ x : ℝ, f (x + p) ≠ f x) ∧ (∀ x : ℝ, g (x + p) ≠ g x) := by

  use (fun _ : ℝ => (0 : ℝ)), (fun _ : ℝ => (0 : ℝ))
  constructor
  · -- Show that for all x, 0 ≤ f(x) ∧ f(x) ≤ 1
    intro x
    constructor
    · -- Show 0 ≤ 0
      norm_num
    · -- Show 0 ≤ 1
      norm_num
  constructor
  · -- Show that for all x, 0 ≤ g(x) ∧ g(x) ≤ 1
    intro x
    constructor
    · -- Show 0 ≤ 0
      norm_num
    · -- Show 0 ≤ 1
      norm_num
  constructor
  · -- Show that there exists p₁ > 0 such that f(x + p₁) = f(x) for all x
    use 1
    constructor
    · -- Show 1 > 0
      norm_num
    · -- Show f(x + 1) = f(x) for all x
      intro x
      simp
  constructor
  · -- Show that there exists p₂ > 0 such that g(x + p₂) = g(x) for all x
    use 1
    constructor
    · -- Show 1 > 0
      norm_num
    · -- Show g(x + 1) = g(x) for all x
      intro x
      simp
  constructor
  · -- Show that there exists p₃ > 0 such that f(x + p₃) + g(x + p₃) = f(x) + g(x) for all x
    use 1
    constructor
    · -- Show 1 > 0
      norm_num
    · -- Show f(x + 1) + g(x + 1) = f(x) + g(x) for all x
      intro x
      simp
  · -- Show ¬∃ p > 0, (∀x, f(x + p) ≠ f(x)) ∧ (∀x, g(x + p) ≠ g(x))
    intro h
    rcases h with ⟨p, hp, hf, hg⟩
    have h1 := hf 0
    norm_num at h1
    all_goals
      contradiction