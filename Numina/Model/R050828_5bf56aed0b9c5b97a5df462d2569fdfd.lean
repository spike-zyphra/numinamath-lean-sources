import Mathlib

theorem number_theory_297301 (n : ℕ) (h₀ : n ∈ Finset.Icc 1000 9999) (h₁ : 11 ∣ n)
    (h₂ : n / 11 = 10 * (Nat.digits 10 n).sum) :
    n = 1980 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₃, h₄⟩
  interval_cases n <;> norm_num at h₁ h₂ ⊢ <;> omega