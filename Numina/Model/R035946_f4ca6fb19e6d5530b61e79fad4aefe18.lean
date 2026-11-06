import Mathlib

theorem number_theory_168335 {n : ℕ} (h₀ : n ∈ Finset.Icc 10 99) (h₁ : 5 ∣ n) (h₂ : ¬3 ∣ n) (h₃ : ¬4 ∣ n)
(h₄ : Even (97 * n)) (h₅ : 6 ≤ n / 10) : n = 70 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₆, h₇⟩
  interval_cases n <;> norm_num [Nat.even_iff] at h₄ h₅ ⊢
  <;> omega