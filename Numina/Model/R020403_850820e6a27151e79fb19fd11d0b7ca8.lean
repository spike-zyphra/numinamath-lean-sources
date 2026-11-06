import Mathlib

theorem algebra_167489 (f : ℝ → ℝ) (hf : ∃ a b c, f = fun x => a * x ^ 2 + b * x + c)
    (h : ∀ x, f (2 * x + 1) = 4 * x ^ 2 + 14 * x + 7) :
    f = fun x => x ^ 2 + 5 * x + 1 := by
  rcases hf with ⟨a, b, c, hf_eq⟩
  have eq1 := h 0
  simp [hf_eq] at eq1
  have eq2 := h 1
  simp [hf_eq] at eq2
  have eq3 := h 2
  simp [hf_eq] at eq3
  have eq4 := h (-1:ℝ)
  simp [hf_eq] at eq4
  have ha : a = 1 := by
    linarith
  have hb : b = 5 := by
    linarith
  have hc : c = 1 := by
    linarith
  funext x
  simp [hf_eq, ha, hb, hc]
  <;> ring