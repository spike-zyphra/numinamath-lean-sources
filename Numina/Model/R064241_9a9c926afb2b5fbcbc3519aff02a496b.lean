import Mathlib

theorem algebra_160916 (f : ℝ → ℝ) (m n : ℝ) (hm : m ≠ 0)
    (hf : ∀ x, f x = m * x ^ 2 + (2 * n + 1) * x - m - 2)
    (h : ∃ x ∈ Set.Icc 3 4, f x = 0) :
    m ^ 2 + n ^ 2 ≥ 1 / 100 := by 
  rcases h with ⟨x, ⟨hx1, hx2⟩, hx3⟩
  have eq : m * x^2 + (2 * n + 1) * x - m - 2 = 0 := by 
    rw [hf x] at hx3 
    linarith
  nlinarith [sq_nonneg (m * x^2 + (2 * n + 1) * x - m - 2), sq_nonneg (x - 3), sq_nonneg (x - 4), 
          sq_nonneg (m + 2 / 25), sq_nonneg (n + 3 / 50)]