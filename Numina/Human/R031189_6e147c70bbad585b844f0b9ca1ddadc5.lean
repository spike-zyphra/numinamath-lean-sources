import Mathlib

theorem algebra_7225 (x y : Fin 3 → ℝ)
    (h₁ : (∑ i, x i) / 3 = 5) (h₂ : (∑ i, y i) / 3 = 7) :
    (∑ i, (2 * x i + 3 * y i)) / 3 = 31 := by 
  have h₁ : ∑ i, x i = 15 := by linarith [h₁]
  have h₂ : ∑ i, y i = 21 := by linarith [h₂]
  have : ∑ i, (2 * x i + 3 * y i) = 93 := by
    calc
      ∑ i, (2 * x i + 3 * y i)
          = 2 * (∑ i, x i) + 3 * (∑ i, y i) := by 
            rw [Finset.sum_add_distrib]
            rw [Finset.mul_sum, Finset.mul_sum]
      _ = 2 * 15 + 3 * 21 := by rw [h₁, h₂]
      _ = 30 + 63 := by norm_num
      _ = 93 := by norm_num
  rw [this]
  norm_num