import Mathlib

open Real Set

theorem inequalities_6146 (x : ℝ) : |x - 1| ≤ 1 / 2 ↔ x ∈ Icc (1 / 2) (3 / 2) := by
  simp only [mem_Icc]
  constructor
  · -- Forward: If |x - 1| ≤ 1/2, then 1/2 ≤ x ∧ x ≤ 3/2
    intro h
    have h1 : -1/2 ≤ x - 1 := by linarith [abs_le.mp h]
    have h2 : x - 1 ≤ 1/2 := by linarith [abs_le.mp h]
    constructor
    · linarith 
    · linarith
  · -- Backward: If 1/2 ≤ x ∧ x ≤ 3/2, then |x - 1| ≤ 1/2
    rintro ⟨h1, h2⟩
    have h3 : -1/2 ≤ x - 1 := by linarith
    have h4 : x - 1 ≤ 1/2 := by linarith
    apply abs_le.mpr
    constructor <;> linarith