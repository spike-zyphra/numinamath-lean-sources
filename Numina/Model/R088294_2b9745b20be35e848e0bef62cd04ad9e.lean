import Mathlib

open Real

theorem number_theory_218943 (a : ℕ → ℤ)
    (h₀ : a 1 = 1966)
    (h₁ : ∀ k, a (k + 1) = ⌊Real.sqrt (∑ i in Finset.Icc 1 k, a i)⌋) :
    a 1966 = 1024 := by 
  have h1 := h₁ 0
  norm_num [Finset.sum_eq_zero] at h1 h₀ 
  all_goals 
    nlinarith