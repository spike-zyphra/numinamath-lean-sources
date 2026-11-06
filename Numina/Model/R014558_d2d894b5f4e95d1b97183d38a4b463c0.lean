import Mathlib

theorem algebra_4841 {f g : ℝ → ℝ} {m: ℝ} (hf : ∀ x, f x = x ^ 2 + 4 * x + 23)
    (hg : ∀ x, g x = x ^ 2 - 6 * x + 2023)
    (hm : IsLeast {g (f x) | x} m) : m = 2270 := by
  have h1 : ∀ x, f x = x ^ 2 + 4 * x + 23 := hf
  have h2 : ∀ x, g x = x ^ 2 - 6 * x + 2023 := hg
  have h3 : g (f (-2)) = 2270 := by
    rw [h1, h2]
    norm_num
  have h4 : m ≤ 2270 := by
    have h5 : g (f (-2)) ∈ {g (f x) | x} := by
      use -2
    have h6 : m ≤ g (f (-2)) := by
      apply hm.2
      exact h5
    linarith [h3, h6]
  have h7 : ∀ x : ℝ, g (f x) ≥ 2270 := by
    intro x
    have hfx : f x = x ^ 2 + 4 * x + 23 := h1 x
    have hgx : g (f x) = (f x) ^ 2 - 6 * (f x) + 2023 := by
      apply h2
    rw [hgx, hfx]
    nlinarith [sq_nonneg (x + 2), sq_nonneg ( (x ^ 2 + 4 * x + 23 ) - 19 ), sq_nonneg ( (x ^ 2 + 4 * x + 23 ) - 3 ) ]
  have h8 : m ≥ 2270 := by
    have h9 : ∀ x : ℝ, g (f x) ≥ 2270 := h7
    have h10 : ∀ y, y ∈ {g (f x) | x} → 2270 ≤ y := by
      intro y hy
      rcases hy with ⟨x, hx⟩
      have h6 : g (f x) ≥ 2270 := h9 x
      linarith [h6, hx]
    have h11 : m ∈ {g (f x) | x} := hm.1
    have h12 : 2270 ≤ m := by
      apply h10 m
      exact h11
    linarith
  linarith [h4, h8]