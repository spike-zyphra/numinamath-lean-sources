import Mathlib


theorem algebra_14758
    (x y : ℝ → ℝ)
    (hinv : ∃ k, (∀ t, x t * y t = k))
    (h : ∀ t, x t + y t = 42 → x t = 2 * y t)
    (h' : ∃ t, x t + y t = 42) :
    ∀ t, x t = -8 → y t = -49 := by
  rcases h' with ⟨t₀, ht₀⟩
  have h₀ : x t₀ + y t₀ = 42 := ht₀
  have h₁ : x t₀ = 2 * y t₀ := h t₀ (ht₀)
  have hy₀ : y t₀ = 14 := by
    linarith
  have hx₀ : x t₀ = 28 := by
    linarith [h₁, hy₀]
  rcases hinv with ⟨k, hk⟩
  have hk₀ : k = 392 := by
    have h₀₀ : x t₀ * y t₀ = k := hk t₀
    rw [hx₀, hy₀] at h₀₀
    nlinarith
    all_goals nlinarith
  intro t ht
  have ht' : x t * y t = k := hk t
  rw [ht] at ht'
  have hy : y t = -49 := by
    rw [show k = 392 by linarith [hk₀]] at ht'
    nlinarith
    all_goals nlinarith
  linarith [hy, ht]
  all_goals nlinarith
  all_goals tauto