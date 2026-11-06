import Mathlib

theorem algebra_321371 (α β : ℕ → ℤ) (h : ∀ n, α n > β n)
    (h1 : ∀ n, α n ^ 2 - 2 * (n + 2) * α n + 3 * (n + 1) = 0)
    (h2 : ∀ n, β n ^ 2 - 2 * (n + 2) * β n + 3 * (n + 1) = 0) :
    ∑ i in Finset.Icc 1 99, (α i : ℝ) / β i = 10098 := by 
  have h11 := h1 1
  have h21 := h2 1
  norm_num at h11 h21 
  have h1_eq : (α 1 : ℤ) ^ 2 - 6 * (α 1 : ℤ) + 6 = 0 := by 
    linarith 
  have h2_eq : (β 1 : ℤ) ^ 2 - 6 * (β 1 : ℤ) + 6 = 0 := by 
    linarith 
  have h3 : (α 1 : ℤ) < 10 := by 
    nlinarith 
  have h4 : (α 1 : ℤ) > -10 := by 
    nlinarith 
  have h5 : (β 1 : ℤ) < 10 := by 
    nlinarith 
  have h6 : (β 1 : ℤ) > -10 := by 
    nlinarith 
  interval_cases h9 : (α 1 : ℤ) <;> 
    interval_cases h10 : (β 1 : ℤ) <;> 
      omega