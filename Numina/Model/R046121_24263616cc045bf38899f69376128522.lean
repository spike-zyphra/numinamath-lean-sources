import Mathlib

theorem algebra_307143 (a : Fin 4 → Fin 4 → ℝ) (k : ℝ)
    (h₀ : ∀ i, ∑ j : Fin 4, a i j = k)
    (h₁ : ∀ j, ∑ i : Fin 4, a i j = k)
    (h₂ : ∑ i : Fin 4, a i i = k)
    (h₃ : ∑ i : Fin 4, a i (3 - i) = k) :
    a 0 0 + a 0 3 + a 3 0 + a 3 3 = k := by

  have eq1 := h₀ 0
  have eq2 := h₀ 1
  have eq3 := h₀ 2
  have eq4 := h₀ 3

  have eq5 := h₁ 0
  have eq6 := h₁ 1
  have eq7 := h₁ 2
  have eq8 := h₁ 3

  have eq9 := h₂
  have eq10 := h₃

  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9 eq10

  linarith