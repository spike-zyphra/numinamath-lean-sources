import Mathlib

theorem algebra_15222 (n : ℕ) (hn : n > 0) :
    ∑ i ∈ Finset.range n, (1 / 3 : ℚ)^i = 121 / 81 ↔ n = 5 := by 
  constructor 
  · -- Forward: if the sum equals 121/81, then n = 5
    intro h_eq 
    have h1 : ∀ n : ℕ, ∑ i in Finset.range n, (1 / 3 : ℚ) ^ i = (1 - (1 / 3 : ℚ) ^ n) / (1 - (1 / 3 : ℚ)) := by
      intro n 
      induction n with 
      | zero => 
        simp 
      | succ n ih => 
        rw [Finset.sum_range_succ, ih] 
        field_simp 
        ring 
    have eq1 : ∑ i in Finset.range n, (1 / 3 : ℚ) ^ i = (1 - (1 / 3 : ℚ) ^ n) / (1 - (1 / 3 : ℚ)) := h1 n 
    rw [eq1] at h_eq 
    have h2 : (1 - (1 / 3 : ℚ) ^ n) / (1 - (1 / 3 : ℚ)) = 121 / 81 := by 
      linarith [h_eq] 
    norm_num at h2 
    have h3 : (1 / 3 : ℚ) ^ n = 1 / 243 := by
      nlinarith 
    have h4 : (1 / 3 : ℚ) ^ n = (1 / 3 : ℚ) ^ 5 := by
      rw [h3]
      norm_num
    have h5 : n = 5 := by 
      exact Nat.cast_injective ((by simpa using h4 : (n : ℕ) = (5 : ℕ)))
    exact h5 
  · -- Backward: if n = 5, then the sum equals 121/81 
    intro h_eq 
    rw [h_eq]
    norm_num [Finset.sum_range_succ]