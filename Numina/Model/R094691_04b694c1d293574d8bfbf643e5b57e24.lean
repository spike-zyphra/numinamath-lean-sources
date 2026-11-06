import Mathlib

theorem number_theory_101150 (n : ℕ) (h₀ : n ∈ Finset.Icc 10 99) (h₁ : (n / 10) < (n % 10))
    (h₂ : n = ∑ i in Finset.Icc (n / 10) (n % 10), i) :
    n = 27 ∨ n = 15 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₃, h₄⟩
  interval_cases n <;> norm_num [Finset.sum_Icc_succ_top, add_assoc] at h₂ <;> omega