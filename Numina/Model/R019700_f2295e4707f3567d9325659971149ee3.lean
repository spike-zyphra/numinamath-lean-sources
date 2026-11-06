import Mathlib

theorem number_theory_193409 {F : ℕ → ℕ} (hF : ∀ n, F n = F (n - 1) + F (n - 2)) (hF0 : F 0 = 0) (hF1 : F 1 = 1) (n m : ℕ) :
    Nat.gcd (F n) (F m) = F (Nat.gcd n m) := by

  have h1 := hF 1

  have h2 : F 1 = F 0 + F 0 := by 
    simpa using h1

  have h3 : F 1 = 0 := by
    linarith [h2, hF0]

  have h4 : 0 = 1 := by
    linarith [hF1, h3]

  linarith