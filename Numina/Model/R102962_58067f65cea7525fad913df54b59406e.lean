import Mathlib

theorem algebra_59249 {n : ℕ} (hn : n > 0) (f : ℕ → ℝ)
    (h₀ : ∀ i ∈ Finset.range (n + 3), f i = 2 ^ i) (h₁ : f (n + 2) = 2 ^ (n + 2) - n - 3) :
    ∃! i ∈ Finset.range (n + 3), f i ≠ 2 ^ i := by
  have h2 : f (n + 2) = 2 ^ (n + 2) := by
    specialize h₀ (n + 2) (Finset.mem_range.mpr (by linarith))
    simpa using h₀
  have h3 : f (n + 2) = 2 ^ (n + 2) - n - 3 := h₁
  have h4 : (2 : ℝ) ^ (n + 2) = (2 : ℝ) ^ (n + 2) - (n : ℝ) - 3 := by 
    linarith [h2, h3]
  have h5 : (n : ℝ) + 3 = 0 := by 
    nlinarith [h4]
  have h6 : (n : ℝ) + 3 > (0 : ℝ) := by
    have hn' : (n : ℝ) > (0 : ℝ) := by
      exact_mod_cast (show n > 0 by linarith)
    linarith
  linarith