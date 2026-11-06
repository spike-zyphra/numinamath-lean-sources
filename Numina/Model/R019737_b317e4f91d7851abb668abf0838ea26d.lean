import Mathlib

theorem algebra_602060 {f : ℝ → ℝ} (hf : ∀ x > 0, f x > 0)
    (h1 : ∀ x y, x > 0 → y > 0 → f (x * f y) = y * f x)
    (h2 : ∀ ε, ∃ x, ∀ y, x < y → f y < ε) :
    ∀ x > 0, f x = 1 / x := by 
  exfalso
  have h3 := h2 (-1)
  rcases h3 with ⟨x, hx⟩
  by_cases h4 : x ≤ 0
  · -- If x ≤ 0, then pick y = 1 > 0
    have h5 := hx 1 (by linarith)
    have : f 1 > 0 := hf 1 (by linarith)
    linarith
  · -- x > 0
    have h5 := hx (x + 1) (by nlinarith)
    have hx_pos : x + 1 > 0 := by linarith
    have h5_pos : f (x + 1) > 0 := hf (x + 1) (by linarith)
    -- The hypothesis h1 says f(f(y)) = y*f(1)
    -- So f(f(y)) is positive when y is, but from h2 with ε = -1
    -- exists x where for all y > x, f(y) < -1, which contradicts f(y) > 0
    linarith