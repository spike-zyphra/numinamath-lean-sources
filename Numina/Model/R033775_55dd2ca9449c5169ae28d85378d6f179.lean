import Mathlib

theorem algebra_246858 (f : ℕ → ℤ)
    (h₀ : ∀ n, f n = ∑ i in Finset.Icc 1 n, i ^ 2) :
    ∀ n, f (n + 3) - 3 * f (n + 2) + 3 * f (n + 1) - f n = 2 := by
  intro n
  simp [h₀ (n + 3), h₀ (n + 2), h₀ (n + 1), h₀ n] 
  <;> simp [Finset.sum_Icc_succ_top, add_assoc, mul_add, add_mul]
  <;> ring