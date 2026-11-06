import Mathlib

theorem number_theory_251871 (N : ℕ) (h₀ : N % 3 = 1) (h₁ : N % 7 = 3) (h₂ : N % 11 = 8)
    (h₃ : N ∈ Finset.Icc 100 999) :
    N ≤ 976 := by
  rw [Finset.mem_Icc] at h₃
  rcases h₃ with ⟨h₄, h₅⟩
  by_contra h
  push_neg at h
  interval_cases N <;> omega