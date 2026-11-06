import Mathlib

theorem algebra_2092
    (x y z : Fin 3 → ℝ)
    (a b c : ℝ)
    (h₁ : a = (∑ i : Fin 3, x i) / 3)
    (h₂ : b = (∑ i : Fin 3, y i) / 3)
    (h₃ : c = (∑ i : Fin 3, z i) / 3) :
    (∑ i : Fin 3, (x i + y i - z i)) / 3 = a + b - c := by
  have h₄ : (∑ i : Fin 3, (x i + y i - z i)) = (∑ i : Fin 3, x i) + (∑ i : Fin 3, y i) - (∑ i : Fin 3, z i) := by 
    simp [Finset.sum, add_assoc, add_sub_assoc, sub_eq_add_neg]
    <;> ring
  rw [h₄]
  rw [h₁, h₂, h₃]
  all_goals
    simp [Finset.sum]
    <;> ring_nf