import Mathlib

theorem number_theory_226591 {F : ℕ → ℕ} (hF : ∀ n, F n = F (n - 1) + F (n - 2)) (hF0 : F 0 = 0) (hF1 : F 1 = 1) :
    ∀ n, Odd n → ¬∃ p k, Nat.Prime p ∧ p ∣ F n ∧ p = 4 * k + 3 := by
  have h2 := hF 1
  have h3 := hF 0
  simp at h2 h3 hF0 hF1
  all_goals omega