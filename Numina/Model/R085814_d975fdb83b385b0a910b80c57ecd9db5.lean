import Mathlib

theorem algebra_3413 (n : ℕ) (h : n ∈ Finset.Icc 1 100) :
    (∑ i in Finset.Icc 1 100, i^2) - n^2 = 335749 ↔ n = 51 := by
  rw [Finset.mem_Icc] at h
  rcases h with ⟨hn1, hn2⟩
  have h1 : ∑ i in Finset.Icc 1 100, i^2 = 338350 := by
    native_decide
  rw [h1]
  constructor
  · -- Forward direction: if sum i^2 - n^2 = 335749, then n = 51
    intro h2
    have h3 : n ≤ 100 := by
      omega
    have h4 : n^2 = 2601 := by
      omega
    have h5 : n = 51 := by
      have h6 : n ≤ 100 := by
        omega
      have h7 : n = 51 := by
        nlinarith
      exact h7
    exact h5
  · -- Backward direction: n = 51 implies sum i^2 - n^2 = 335749
    intro h5
    rw [h5]
    all_goals omega