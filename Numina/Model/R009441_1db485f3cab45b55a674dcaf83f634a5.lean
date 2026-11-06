import Mathlib

theorem algebra_19711 (a : Fin 6 → ℕ)
    (h₀ : a 0 = 14) (h₁ : a 1 = 5) (h₂ : a 2 = 9)
    (h₃ : a 3 = 7) (h₄ : a 4 = 7) (h₅ : a 5 = 8) :
    (∑i, a i * (i + 1))/(∑i, a i : ℝ) = 3.24 := by
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, h₀, h₁, h₂, h₃, h₄, h₅]
  norm_num