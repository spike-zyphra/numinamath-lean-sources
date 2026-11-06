import Mathlib

theorem algebra_123037 (a : Fin 10 → ℕ) (h₀ : ∑ i, a i = 150)
    (h₁ : ∀ i j, i < j → a i < a j) (h₂ : a 0 ≥ (1 / 2 : ℚ) * a 9) :
    a 5 = 16 := by
  have h3 : a 0 < a 1 := h₁ 0 1 (by simp)
  have h4 : a 1 < a 2 := h₁ 1 2 (by simp)
  have h5 : a 2 < a 3 := h₁ 2 3 (by simp)
  have h6 : a 3 < a 4 := h₁ 3 4 (by simp)
  have h7 : a 4 < a 5 := h₁ 4 5 (by simp)
  have h8 : a 5 < a 6 := h₁ 5 6 (by simp)
  have h9 : a 6 < a 7 := h₁ 6 7 (by simp)
  have h10 : a 7 < a 8 := h₁ 7 8 (by simp)
  have h11 : a 8 < a 9 := h₁ 8 9 (by simp)
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at h₀
  have h13 : (2 * (a 0 : ℚ) ≥ (a 9 : ℚ)) := by
    linarith
  have h14 : 2 * a 0 ≥ a 9 := by
    have h15 : (2 * a 0 : ℚ) ≥ (a 9 : ℚ) := h13
    norm_num at h15 ⊢
    exact_mod_cast h15
  omega