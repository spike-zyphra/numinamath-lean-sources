import Mathlib

theorem number_theory_236936 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : (Nat.digits 10 n).sum = 4) :
    n = 400 ∨ n = 310 ∨ n = 301 ∨ n = 130 ∨ n = 103 ∨ n = 220 ∨ n = 202 ∨ n = 211 ∨ n = 121 ∨ n = 112 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₂, h₃⟩
  interval_cases n <;> norm_num at h₁ ⊢
  <;> omega