import Mathlib

theorem number_theory_7282 (F : ℕ → ℕ) (hF : ∀ n, F n = F (n - 1) + F (n - 2)) (hF0 : F 0 = 0) (hF1 : F 1 = 1) (k : ℕ) (hk : 0 < k) :
    Nat.Coprime (F (4 * k)) (F (4 * k + 2)) := by 
  have h1 := hF 1
  simp at h1
  all_goals omega