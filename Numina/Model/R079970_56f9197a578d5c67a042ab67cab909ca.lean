import Mathlib

theorem number_theory_284244 (n : ℕ) (h₀ : n ∈ Finset.Icc 10 99) (h₁ : 2110 % n = 5) :
    n = 15 ∨ n = 21 ∨ n = 35 := by 
  have h2 : n ≥ 10 := Finset.mem_Icc.mp h₀ |>.1
  have h3 : n ≤ 99 := Finset.mem_Icc.mp h₀ |>.2
  interval_cases n <;> norm_num at h₁ <;> tauto