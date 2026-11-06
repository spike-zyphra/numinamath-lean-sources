import Mathlib

theorem algebra_7225 (x y : Fin 3 → ℝ)
    (h₁ : (∑ i, x i) / 3 = 5) (h₂ : (∑ i, y i) / 3 = 7) :
    (∑ i, (2 * x i + 3 * y i)) / 3 = 31 := by
  have h3 : ∑ i : Fin 3, x i = 15 := by
    have eq1 : (∑ i, x i) / 3 = 5 := h₁
    have eq2 : ∑ i, x i = 15 := by
      linarith
    exact_mod_cast eq2
  have h4 : ∑ i : Fin 3, y i = 21 := by
    have eq1 : (∑ i, y i) / 3 = 7 := h₂
    have eq2 : ∑ i, y i = 21 := by
      linarith
    exact_mod_cast eq2
  have h5 : ∑ i : Fin 3, (2 * x i + 3 * y i) = 2 * (∑ i : Fin 3, x i) + 3 * (∑ i : Fin 3, y i) := by 
    simp [Finset.sum, add_mul, mul_add]
    <;> ring
  rw [h5]
  rw [h3, h4]
  norm_num