import Mathlib

theorem number_theory_165818 (n : ℕ) (h₀ : n ∈ Finset.Icc 10 99) :
    1477 % n = 49 ↔ n = 51 ∨ n = 68 ∨ n = 84 := by 
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₁₀, h₂₀⟩
  constructor
  · -- Forward implication: If 1477 % n = 49, then n = 51 or n = 68 or n = 84
    intro h
    interval_cases n <;> norm_num at h ⊢ <;> omega
  · -- Backward implication: If n = 51 or n = 68 or n = 84, then 1477 % n = 49
    rintro (h | h | h)
    · -- Case n = 51
      subst h
      norm_num
    · -- Case n = 68
      subst h
      norm_num
    · -- Case n = 84
      subst h
      norm_num