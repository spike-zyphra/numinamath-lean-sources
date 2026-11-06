import Mathlib

theorem algebra_104852 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : ∃ k, Even k ∧ k ∈ Finset.Icc 10 99 ∧ n - k = 3) :
    n = 101 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₁ with ⟨k, hk_even, hk_in_range, h_diff⟩
  rw [Finset.mem_Icc] at hk_in_range
  rcases hk_in_range with ⟨hk1, hk2⟩
  have h4 : k % 2 = 0 := by 
    exact Nat.even_iff.1 hk_even
  have h5 : n = k + 3 := by 
    omega
  have h6 : k ≥ 97 := by 
    linarith [h5, h₀.1]
  have h7 : k ≤ 99 := by 
    linarith
  have hk8 : k = 98 := by 
    interval_cases k <;> omega
  omega