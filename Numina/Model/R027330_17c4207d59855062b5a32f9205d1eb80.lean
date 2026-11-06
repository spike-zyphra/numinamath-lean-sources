import Mathlib

theorem number_theory_226474 (F : ℕ → ℕ) (hF : ∀ n, F n > 0)
    (hF1 : ∀ n, F n = F (n - 1) + F (n - 2)) (hF2 : F 0 = 1) (hF3 : F 1 = 1) :
    ∀ n m, Nat.Coprime (F n) (F (n + 1)) ∧
    Nat.gcd (F m) (F n) = F (Nat.gcd m n) := by
  have h1 := hF1 0
  simp [hF2] at h1
  all_goals omega