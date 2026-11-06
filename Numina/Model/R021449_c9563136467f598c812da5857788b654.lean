import Mathlib

theorem algebra_231495 {f : ℝ → ℝ} (h : ∀ x y, f x * f y = f (x - y)) (h' : ∃ x, f x ≠ 0) :
    ∀ x, f x = 1 := by
  rcases h' with ⟨x₀, hx₀⟩
  have h1 : f 0 = 1 := by
    have hx₀0 : f x₀ * f 0 = f x₀ := by
      specialize h x₀ (0 : ℝ)
      simpa using h
    have hx₀_ne_zero : f x₀ ≠ 0 := hx₀
    have eq1 : f x₀ * f 0 = f x₀ := hx₀0
    field_simp [hx₀_ne_zero] at eq1 ⊢
    <;> nlinarith
  have h4 : ∀ x : ℝ, f x ^ 2 = 1 := by
    intro x
    have h5 : f x * f x = f (x - x : ℝ) := h x x
    have h6 : x - x = (0 : ℝ) := by ring_nf
    rw [h6] at h5
    rw [h1] at h5
    nlinarith
  have h5 : ∀ x : ℝ, f x = 1 := by
    intro x
    have h5 : f x * f (x / 2) = f (x / 2) := by
      have eq1 := h x (x / 2)
      have eq2 : x - (x / 2 : ℝ) = x / 2 := by ring_nf
      rw [eq2] at eq1
      linarith [eq1]
    have hx2_ne_zero : f (x / 2) ≠ 0 := by
      have h7 : f (x / 2) ^ 2 = 1 := h4 (x / 2)
      have h8 : f (x / 2) ≠ 0 := by
        by_contra h9
        rw [h9] at h7
        nlinarith
      exact h8
    have hx_eq_1 : f x = 1 := by
      have h6 : f (x / 2) * (f x - 1) = 0 := by
        -- Expand f(x/2)(f(x) - 1) = f(x/2)f(x) - f(x/2)
        -- From h5: f(x)f(x/2) = f(x/2)
        -- So this is: f(x/2)f(x) - f(x/2) = f(x/2)(f(x)-1)
        have eq1 : f x * f (x / 2) = f (x / 2) := h5
        linarith [eq1]
      cases' (mul_eq_zero.1 h6) with h7 h8
      · -- contradiction since f (x / 2) ≠ 0
        exfalso
        have : f (x / 2) = 0 := by
          linarith [h7]
        tauto
      · -- conclusion f x - 1 = 0
        linarith
    exact hx_eq_1
  intro x
  exact h5 x