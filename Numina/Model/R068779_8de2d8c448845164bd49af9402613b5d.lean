import Mathlib

theorem algebra_22004 : (MeasureTheory.volume {x : ℝ | (x - 4) ^ 2 ≤ 9}).toReal = 6 := by
  have h1 : {x : ℝ | (x - 4) ^ 2 ≤ 9} = Set.Icc (1 : ℝ) (7 : ℝ) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · -- Forward: If (x - 4)^2 ≤ 9, then 1 ≤ x ≤ 7
      intro h
      have h2 : (x - 4) ^ 2 ≤ 9 := h
      have h3 : -3 ≤ x - 4 := by nlinarith
      have h4 : x - 4 ≤ 3 := by nlinarith
      constructor
      · linarith
      · linarith
    · -- Backward: If 1 ≤ x ≤ 7, then (x - 4)^2 ≤ 9
      rintro ⟨h1, h2⟩
      nlinarith
  rw [h1]
  simp
  all_goals norm_num