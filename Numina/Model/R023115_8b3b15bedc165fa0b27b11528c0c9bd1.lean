import Mathlib

open Real

theorem inequalities_289280 {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
    (s : ℝ) (h₀ : ∑ i : Fin n, a i = s) :
    (∀ i : Fin n, a i > sqrt (2 + sqrt 5)) →
    ∏ i : Fin n, (a i + 1 / a i) ≤ ((s / n) + (n / s)) ^ n ∧
    (∀ i : Fin n, 0 < a i ∧ a i < sqrt (2 + sqrt 5)) →
    ∏ i : Fin n, (a i + 1 / a i) ≥ ((s / n) + (n / s)) ^ n := by
  intro h1 h2
  have h3 : ∀ i : Fin n, a i > sqrt (2 + sqrt 5) := h1
  have h4 : ∀ i : Fin n, 0 < a i ∧ a i < sqrt (2 + sqrt 5) := by 
    exact h2.right
  have h5 : n > 0 := by linarith
  have h6 : a ⟨0, by linarith⟩ > sqrt (2 + sqrt 5) := by
    apply h3
  have h7 : a ⟨0, by linarith⟩ < sqrt (2 + sqrt 5) := by 
    have h8 : 0 < a ⟨0, by linarith⟩ ∧ a ⟨0, by linarith⟩ < sqrt (2 + sqrt 5) := by 
      apply h4
    linarith
  linarith