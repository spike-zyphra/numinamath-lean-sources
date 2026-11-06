import Mathlib

theorem number_theory_198436 {n : ℕ} (h₀ : n ∈ Finset.Icc 100 999) (h₁ : 312837 % n = 310650 % n) :
    312837 % n = 96 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₂, h₃⟩
  interval_cases n <;> norm_num at h₁ ⊢ <;> trivial