import Mathlib

theorem number_theory_149615 (a b : Fin 2019 → ℝ)
    (ha : ∀ i j, a i = a j → i = j)
    (hb : ∀ i j, b i = b j → i = j)
    (h : ∀ i, ∃ x y, x ≠ y ∧ a i + b i = x + y ∧ ∃ q : ℚ, x + y = q) :
    {i | ¬(∃ j, a i = j ∨ b i = j)}.encard ≤ 2016 := by
  have h1 := h 0
  rcases h1 with ⟨x, y, hxy, heq, q, hq⟩
  have h2 := h 1
  rcases h2 with ⟨x1, y1, hxy1, heq1, q1, hq1⟩
  have h3 := ha 0 0
  simp at h3
  have h4 := hb 0 0
  simp at h4
  all_goals simp [Set.encard_univ] at *
  all_goals linarith