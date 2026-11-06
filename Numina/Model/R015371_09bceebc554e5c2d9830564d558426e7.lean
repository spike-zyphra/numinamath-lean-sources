import Mathlib

theorem algebra_221652 {f : ℝ → ℝ} (h : ∀ x y, f (x + y) = f x * f y)
    (h' : ∃! x, f x = 1987) :
    ∀ x y, f x = f y → x = y := by
  rcases h' with ⟨x₀, hx₀, h₀⟩
  have h1 : f 0 = 1 := by
    have h00 := h 0 0
    simp at h00 
    have h_ne_zero : f 0 ≠ 0 := by
      by_contra h0
      have h1 : f x₀ = 0 := by
        specialize h x₀ 0
        simp [h0] at h 
        simpa using h
      linarith [hx₀, h1]
    have : f 0 * (f 0 - 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp this) with h₂ h₃
    · contradiction
    · linarith
  intro x y hxy
  have h2 : ∀ z, f (x + z) = f (y + z) := by
    intro z
    have h3 : f (x + z) = f x * f z := h x z
    have h4 : f (y + z) = f y * f z := h y z
    rw [hxy] at h3
    linarith [h3, h4]
  have h5 : x = y := by
    have h6 : f (y + (x₀ - x)) = 1987 := by
      have h4 : ∀ z, f (x + z) = f (y + z) := h2
      specialize h4 (x₀ - x)
      rw [show x + (x₀ - x) = x₀ by linarith] at h4
      linarith [hx₀, h4]
    have h7 : y + (x₀ - x) = x₀ := by 
      apply h₀ 
      linarith 
    linarith 
  exact h5