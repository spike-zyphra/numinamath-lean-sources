import Mathlib

theorem algebra_127711 {a : ℝ} (f : ℝ → ℝ) (h₀ : ∀ x y, f (x + y) = f x * f (a - y) + f y * f (a - x)) (h₁ : f 0 = 1 / 2) :
    ∃ c, ∀ x, f x = c := by
  -- Substitute x = y = 0.
  -- This gives f(0) = 2 * f(0) * f(a).
  -- Since f(0) = 1/2, so 1/2 = 2 * (1/2) * f(a) → f(a) = 1/2.
  have ha : f a = 1 / 2 := by
    have h2 := h₀ 0 0
    simp [h₁] at h2
    linarith
  -- Substitute y = 0 and general x.
  -- This gives f(x) = f(x) * f(a) + f(0) * f(a - x).
  -- Since f(a) = 1/2 and f(0) = 1/2, so f(x) = (1/2) * f(a - x) + (1/2) * f(x).
  -- Rearranging gives f(x) = f(a - x).
  have h2 : ∀ x : ℝ, f x = f (a - x) := by
    intro x
    have h4 := h₀ x 0
    simp [h₁, ha] at h4
    linarith
  -- Substitute y = a - x.
  -- Then f(a) = f(x)^2 + f(a - x)^2 = 2f(x)^2.
  -- Since f(a) = 1/2, so 2f(x)^2 = 1/2 → f(x)^2 = 1/4.
  have h3 : ∀ x : ℝ, f x ^ 2 = 1 / 4 := by
    intro x
    have h4 := h₀ x (a - x)
    have h5 : x + (a - x) = a := by ring
    rw [h5] at h4
    have h6 : f (a - (a - x)) = f x := by
      have h7 : a - (a - x) = x := by ring
      rw [h7]
    rw [h6] at h4
    have h7 : f (a - x) = f x := by
      linarith [h2 x]
    rw [h7] at h4
    nlinarith [ha]
  -- Substitute y = x.
  -- This gives f(2x) = 2 * f(x) * f(a - x).
  -- Since f(a - x) = f(x) and f(x)^2 = 1/4, so f(2x) = 2 * (1/4) = 1/2.
  have h4 : ∀ x : ℝ, f (2 * x) = 1 / 2 := by
    intro x
    have h5 := h₀ x x
    have h6 : x + x = 2 * x := by ring
    rw [h6] at h5
    have h7 : f (a - x) = f x := by
      linarith [h2 x]
    rw [h7] at h5
    nlinarith [h3 x]
  use 1 / 2
  intro x
  -- We need to show that f(x) = 1/2 for all x.
  -- Let's take x/2 and use h4.
  -- From h4, we have f(2 * (x/2)) = 1/2.
  -- But 2 * (x/2) = x, so f(x) = 1/2.
  have h5 : f x = 1 / 2 := by
    -- Let's take x/2 and use h4.
    -- From h4, we have f(2 * (x/2)) = 1/2.
    -- But 2 * (x/2) = x, so f(x) = 1/2.
    have h7 : f (2 * (x / 2)) = 1 / 2 := h4 (x / 2)
    have h8 : 2 * (x / 2) = x := by ring
    rw [h8] at h7
    linarith
  exact h5