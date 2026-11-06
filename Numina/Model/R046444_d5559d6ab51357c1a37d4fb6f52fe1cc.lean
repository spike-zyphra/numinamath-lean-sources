import Mathlib

theorem algebra_326634 {f : ℝ → ℝ} (h : ∀ x, f (f x - x^2 + x) = f x - x^2 + x)
    (h' : ∃! x, f x = x) :
    ∀ x, f x = x^2 - x + 1 := by
  rcases h' with ⟨x₀, hx₀, hx₁⟩
  have h1 : f (2 * x₀ - x₀^2) = 2 * x₀ - x₀^2 := by
    have h2 : f (f x₀ - x₀^2 + x₀) = f x₀ - x₀^2 + x₀ := h x₀
    rw [hx₀] at h2
    ring_nf at h2 ⊢
    linarith
  have h2 : 2 * x₀ - x₀^2 = x₀ := by
    have h3 : f (2 * x₀ - x₀^2) = 2 * x₀ - x₀^2 := h1
    have h4 : 2 * x₀ - x₀^2 = x₀ := by
      apply hx₁ (2 * x₀ - x₀^2)
      linarith
    linarith
  have h3 : x₀ * (x₀ - 1) = 0 := by
    nlinarith
  have h4 : x₀ = 0 ∨ x₀ = 1 := by
    cases (mul_eq_zero.mp h3) with
    | inl h5 => 
      left
      linarith
    | inr h6 => 
      right
      linarith
  have h5 : x₀ = 1 := by
    cases h4 with
    | inl h6 =>
      -- Case x₀ = 0
      have h7 : f 1 = 0 := by
        have h8 : f (f 1) = f 1 := by
          have h9 : f (f 1 - 1^2 + 1) = f 1 - 1^2 + 1 := h 1
          norm_num at h9 ⊢
          linarith
        have h13 : f 1 = x₀ := by
          have h12 : f (f 1) = f 1 := h8
          apply hx₁ (f 1)
          linarith
        rw [show x₀ = (0 : ℝ) by linarith [h6]] at h13
        linarith
      have h14 : f (f 2 - 2) = f 2 - 2 := by
        have h15 : f (f 2 - 2^2 + 2) = f 2 - 2^2 + 2 := h 2
        ring_nf at h15 ⊢
        linarith
      have h17 : f 2 - 2 = x₀ := by
        have h18 : f (f 2 - 2) = f 2 - 2 := h14
        have h19 : f 2 - 2 = x₀ := by
          apply hx₁ (f 2 - 2)
          linarith
        linarith
      have h18 : f 2 = 2 := by
        rw [show x₀ = (0 : ℝ) by linarith [h6]] at h17
        nlinarith [h17, h14]
      have h20 : 2 = x₀ := by
        have h21 : f 2 = 2 := h18
        have h22 : f 2 = 2 := h18
        have h23 : 2 = x₀ := by
          apply hx₁ 2
          linarith
        linarith
      linarith
    | inr h7 =>
      linarith
  intro x
  have h7 : f (f x - x^2 + x) = f x - x^2 + x := h x
  have h9 : f x - x^2 + x = x₀ := by
    have h10 : f (f x - x^2 + x) = f x - x^2 + x := h7
    have h11 : f x - x^2 + x = x₀ := by
      apply hx₁ (f x - x^2 + x)
      linarith
    linarith
  rw [h5] at h9
  nlinarith