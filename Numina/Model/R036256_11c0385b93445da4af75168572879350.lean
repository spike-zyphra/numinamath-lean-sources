import Mathlib

theorem other_266994 (T : ℝ) (hT : T > 0) :
    (MeasureTheory.volume {x | x ∈ Set.Icc 0 T ∧ x % 5 = 0 ∧ x % 7 ≠ 0}).toReal =
    (MeasureTheory.volume {x | x ∈ Set.Icc 0 T ∧ x % 5 ≠ 0 ∧ x % 7 = 0}).toReal / 14 := by 
  have h1 : {x | x ∈ Set.Icc 0 T ∧ x % 5 = 0 ∧ x % 7 ≠ 0} = ∅ := by
    ext x
    simp
  have eq1 : (MeasureTheory.volume {x | x ∈ Set.Icc 0 T ∧ x % 5 = 0 ∧ x % 7 ≠ 0}).toReal = 0 := by 
    rw [h1]
    simp
  have h2 : {x | x ∈ Set.Icc 0 T ∧ x % 5 ≠ 0 ∧ x % 7 = 0} = ∅ := by 
    ext x
    simp
  have eq2 : (MeasureTheory.volume {x | x ∈ Set.Icc 0 T ∧ x % 5 ≠ 0 ∧ x % 7 = 0}).toReal = 0 := by 
    rw [h2]
    simp
  rw [eq1, eq2]
  norm_num