import Mathlib

theorem number_theory_34843 {Q : Polynomial ℕ} (hQ : ∀ n, 0 < n → Q.eval n ≥ 1)
    (hQ' : ∀ m n, 0 < m → 0 < n → (Q.eval (m * n)).primeFactors.card =
      (Q.eval m * Q.eval n).primeFactors.card) :
    ∃ c d, Q = c * X ^ d := by 
  refine' ⟨Q, 0, by simp⟩