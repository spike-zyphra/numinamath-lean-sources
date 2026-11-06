import Mathlib

theorem number_theory_118056 (r : Fin 50 → ℚ) (ir : Fin 50 → ℝ)
    (hr : ∀ i, r i ≠ 0) (hri : ∀ i, ir i ≠ 0)
    (hriq : ∀ i, Irrational (ir i)) :
    {i | ∃ j, ¬Irrational (r i * ir j)}.encard ≤ 1275 := by
  have h1 : ∀ i, ∀ j, Irrational (r i * ir j) := by
    intro i j
    have hri' : ¬ Irrational (r i) := by simp
    have h3 : Irrational (ir j) := hriq j
    have hrne : r i ≠ 0 := hr i
    have h : Irrational (r i * ir j) := by
      rw [mul_comm]
      apply Irrational.mul_rat
      · exact h3
      · exact hrne
    exact h
  have h2 : {i | ∃ j, ¬Irrational (r i * ir j)} = ∅ := by
    ext i
    simp
    intro j
    have h1' : Irrational (r i * ir j) := h1 i j
    simpa using h1'
  rw [h2]
  simp [Set.encard_empty]