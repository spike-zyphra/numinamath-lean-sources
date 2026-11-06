import Mathlib

theorem number_theory_205954 (a : Fin 5 → ℝ)
    (h₀ : ∑ i, a i = 1500)
    (h₁ : ∀ i, a i ≥ 0) :
    ∃ i, a i < 320 := by
  -- Assume, towards contradiction, that all persons have at least 320.
  by_contra h
  push_neg at h
  -- Then, the total salary should be at least 5 * 320 = 1600.
  have h2 : ∑ i : Fin 5, a i ≥ 1600 := by 
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at *
    -- Use the assumption that each a i >= 0, so they must each be >= 320
    linarith [h 0, h 1, h 2, h 3, h 4]
  -- But the total salary is only 1500.
  have h3 : ∑ i : Fin 5, a i = 1500 := h₀
  -- Derive a contradiction.
  linarith