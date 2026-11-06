import Mathlib

theorem algebra_205627 (a : Fin 4 → ℝ) (ha : ∀ i, a i ∈ Set.Ioo (-1) 1) :
    1 + a 0 / (1 - a 0) + a 1 / (1 - a 0) / (1 - a 1) +
    a 2 / (1 - a 0) / (1 - a 1) / (1 - a 2) +
    (a 3 - a 0) / (1 - a 0) / (1 - a 1) / (1 - a 2) / (1 - a 3) =
    1 / ((1 - a 1) * (1 - a 2) * (1 - a 3)) := by

  have h1 : ∀ i, -1 < a i ∧ a i < 1 := by
    intro i
    specialize ha i
    simpa using ha

  have ha01 : 1 - a 0 ≠ 0 := by
    have h0 : -1 < a 0 ∧ a 0 < 1 := h1 0
    linarith

  have ha11 : 1 - a 1 ≠ 0 := by
    have h11 : -1 < a 1 ∧ a 1 < 1 := h1 1
    linarith

  have ha21 : 1 - a 2 ≠ 0 := by
    have h21 : -1 < a 2 ∧ a 2 < 1 := h1 2
    linarith

  have ha31 : 1 - a 3 ≠ 0 := by
    have h31 : -1 < a 3 ∧ a 3 < 1 := h1 3
    linarith

  field_simp [ha01, ha11, ha21, ha31]
  <;> ring