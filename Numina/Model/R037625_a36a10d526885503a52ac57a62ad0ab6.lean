import Mathlib

theorem inequalities_234903 (a : Fin 19 → ℝ) (h : ∀ i j k, i + 1 = j ∧ j + 1 = k → a i + a j + a k > 0)
    (ha : ∑ i, a i < 0) :
    False := by
  have h1 := h 0 1 2 ⟨rfl, rfl⟩
  have h2 := h 1 2 3 ⟨rfl, rfl⟩
  have h3 := h 2 3 4 ⟨rfl, rfl⟩
  have h4 := h 3 4 5 ⟨rfl, rfl⟩
  have h5 := h 4 5 6 ⟨rfl, rfl⟩
  have h6 := h 5 6 7 ⟨rfl, rfl⟩
  have h7 := h 6 7 8 ⟨rfl, rfl⟩
  have h8 := h 7 8 9 ⟨rfl, rfl⟩
  have h9 := h 8 9 10 ⟨rfl, rfl⟩
  have h10 := h 9 10 11 ⟨rfl, rfl⟩
  have h11 := h 10 11 12 ⟨rfl, rfl⟩
  have h12 := h 11 12 13 ⟨rfl, rfl⟩
  have h13 := h 12 13 14 ⟨rfl, rfl⟩
  have h14 := h 13 14 15 ⟨rfl, rfl⟩
  have h15 := h 14 15 16 ⟨rfl, rfl⟩
  have h16 := h 15 16 17 ⟨rfl, rfl⟩
  have h17 := h 16 17 18 ⟨rfl, rfl⟩
  have h18 := h 17 18 0 ⟨by simp, by simp⟩
  have h19 := h 18 0 1 ⟨by simp, by simp⟩
  have h20 : ∑ i : Fin 19, a i > 0 := by
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at *
    linarith
  linarith