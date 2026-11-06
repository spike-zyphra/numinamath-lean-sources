import Mathlib

theorem number_theory_1517 (n : ℕ) (h₀ : n^2 ∈ Finset.Icc 1000 9999) (h₁ : (n^2)/1000 = 4) (h₂ : n^2 ≡ 5 [MOD 10]) :
    n = 65 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₃, h₄⟩
  have h₅ : n ≤ 99 := by nlinarith
  have h₆ : n ≥ 32 := by nlinarith
  interval_cases n <;> norm_num [Nat.ModEq] at h₂ h₁ ⊢ <;> omega