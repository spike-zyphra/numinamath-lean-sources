import Mathlib

theorem inequalities_122005 (a : Fin 7 → ℝ) (h : ∀ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k → a i + a j + a k < ∑ l, a l - a i - a j - a k) :
    ∀ i, 0 < a i := by
  have h1 := h 0 1 2 ⟨by simp, by simp, by simp⟩
  have h2 := h 0 3 4 ⟨by simp, by simp, by simp⟩
  have h3 := h 0 5 6 ⟨by simp, by simp, by simp⟩
  have h4 := h 1 2 3 ⟨by simp, by simp, by simp⟩
  have h5 := h 1 4 5 ⟨by simp, by simp, by simp⟩
  have h6 := h 1 3 6 ⟨by simp, by simp, by simp⟩
  have h7 := h 2 3 4 ⟨by simp, by simp, by simp⟩
  have h8 := h 2 5 6 ⟨by simp, by simp, by simp⟩
  have h9 := h 3 4 5 ⟨by simp, by simp, by simp⟩
  have h10 := h 3 4 6 ⟨by simp, by simp, by simp⟩
  have h11 := h 4 5 6 ⟨by simp, by simp, by simp⟩
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  intro i
  have h12 : 0 < a 0 := by
    linarith
  have h13 : 0 < a 1 := by
    linarith
  have h14 : 0 < a 2 := by
    linarith
  have h15 : 0 < a 3 := by
    linarith
  have h16 : 0 < a 4 := by
    linarith
  have h17 : 0 < a 5 := by
    linarith
  have h18 : 0 < a 6 := by
    linarith
  have h19 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by
    fin_cases i <;> simp
  rcases h19 with (r | r | r | r | r | r | r)
  · rw [r]
    exact h12
  · rw [r]
    exact h13
  · rw [r]
    exact h14
  · rw [r]
    exact h15
  · rw [r]
    exact h16
  · rw [r]
    exact h17
  · rw [r]
    exact h18