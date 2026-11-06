import Mathlib

open Real

theorem algebra_264378 {f g : ℝ → ℝ} (hf : f = fun x => (1 - 2^x) / (1 + 2^x))
    (hg : ∀ x, ∃! y, g x = y ∧ f y = x) :
    g (2 / 7) = logb 2 (5 / 9) := by

  have h1 : ∀ x, ∃! y, g x = y ∧ f y = x := hg

  -- Apply the property to x = 2/7
  have h2 := h1 (2 / 7)
  rcases h2 with ⟨y, ⟨hy_eq, hf_eq⟩, h2_unique⟩

  -- f(y) = 2/7
  rw [hf] at hf_eq

  simp at hf_eq
  -- Solve the equation (1 - 2^y) / (1 + 2^y) = 2 / 7
  have eq1 : (1 + (2:ℝ) ^ y) ≠ 0 := by
    by_contra h
    have : (1 + (2:ℝ) ^ y) = 0 := by linarith
    have h2y_pos : (2:ℝ) ^ y > 0 := by positivity
    nlinarith

  have eq3 : (1 - (2 : ℝ) ^ y) = (2 / 7 : ℝ) * (1 + (2 : ℝ) ^ y) := by
    field_simp at hf_eq ⊢
    nlinarith

  have eq4 : (2 : ℝ) ^ y = (5 / 9 : ℝ) := by
    nlinarith [eq3]

  -- Therefore, y = logb 2 (5 / 9)
  have hy : y = logb 2 (5 / 9 : ℝ) := by
    have h1 : (2 : ℝ) ^ y = (5 / 9 : ℝ) := eq4
    have h2 : y = Real.logb 2 (5 / 9 : ℝ) := by
      rw [← h1]
      field_simp
    exact h2

  -- g(2/7) = y
  have g_eq_y : g (2 / 7 : ℝ) = y := by
    linarith [hy_eq]

  rw [g_eq_y]
  rw [hy]