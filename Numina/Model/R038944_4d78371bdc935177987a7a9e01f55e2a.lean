import Mathlib

theorem number_theory_226481 (F : ℕ → ℕ) (hF : ∀ n, F n = F (n - 1) + F (n - 2)) (hF0 : F 0 = 0) (hF1 : F 1 = 1) (m n : ℕ) (hm : m > 2) :
    F m ∣ F n ↔ m ∣ n := by
  have h1 := hF 1
  have h2 := hF 0
  simp [hF0, hF1] at h1 h2
  all_goals omega