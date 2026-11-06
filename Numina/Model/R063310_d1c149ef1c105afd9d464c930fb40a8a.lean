import Mathlib

theorem number_theory_4967 (n : ℕ) (h₀ : n ∈ Finset.Icc 1000 9999) (h₁ : Nat.gcd n 1764 = 294) :
    n ≤ 9114 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₃, h₄⟩
  by_contra h
  push_neg at h
  interval_cases n <;> norm_num [Nat.gcd] at h₁ ⊢
  all_goals omega