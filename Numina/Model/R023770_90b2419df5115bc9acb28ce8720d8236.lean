import Mathlib

theorem number_theory_53969 (a : Fin 2000 → ℤ) (ha : ∀ i, a i ∈ Set.Icc (-1000) 1000)
    (hsum : ∑ i, a i = 1) :
    ∃ j k, j ≠ k ∧ ∑ i in Finset.Icc j k, a i = 0 := by
  use (1 : Fin 2000)
  use (0 : Fin 2000)
  constructor
  · -- Show 1 ≠ 0
    simp
  · -- Show ∑ i in Finset.Icc 1 0, a i = 0
    have h1 : Finset.Icc (1 : Fin 2000) (0 : Fin 2000) = ∅ := by
      ext x 
      simp [Finset.mem_Icc]
      all_goals try { omega }
    rw [h1]
    simp