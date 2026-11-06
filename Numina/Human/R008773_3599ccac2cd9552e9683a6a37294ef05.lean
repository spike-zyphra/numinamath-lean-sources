import Mathlib

/- The sum of the squares of three consecutive positive even numbers is $12296$. Find the product of the three numbers divided by $8$. -/
theorem algebra_21458 (n : ℕ) (h₀ : Even n) (h₁ : ∑ i ∈ Finset.range 3, (n + 2 * i)^2 = 12296) :
    (n * (n + 2) * (n + 4)) / 8 = 32736 := by
  simp only [Finset.sum_range, Fin.sum_univ_three, Fin.isValue, Fin.val_zero, mul_zero, add_zero, Fin.val_one, mul_one, Fin.val_two, Nat.reduceMul] at h₁
  have neq : n = 62 := by
    nlinarith
  rw [neq]