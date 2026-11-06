import Mathlib

theorem number_theory_187431 {n : ℕ} (h₀ : n ∈ Finset.Icc 100 999) (h₁ : n^2 = (n % 100)^2 + (n / 100)^2)
    (h₂ : ∃ m, m ∈ Finset.Icc 100 999 ∧ m^2 = (m % 100)^2 + (m / 100)^2 ∧ Nat.digits 10 n = List.reverse (Nat.digits 10 m)) :
    n = 333 ∨ n = 666 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₃, h₄⟩
  exfalso
  have h5 : n ^ 2 > (n % 100) ^ 2 + (n / 100) ^ 2 := by
    have h3 : n ≥ 100 := by omega
    have h4 : n / 100 ≥ 1 := by
      omega
    have h7 : n = 100 * (n / 100) + (n % 100) := by
      omega
    nlinarith [sq_pos_of_pos (show 0 < (n / 100 : ℕ) by omega), 
      sq_nonneg (n % 100), sq_nonneg (n / 100), 
      mul_nonneg (show 0 ≤ (n / 100 : ℕ) by omega) (show 0 ≤ (n % 100 : ℕ) by omega)
    ]
  omega