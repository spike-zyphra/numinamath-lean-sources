import Mathlib

theorem number_theory_69940 (m n : ℕ) (hmn : Nat.Coprime m n)
    (h : ∃ f : Polynomial ℕ, f.degree > 0 ∧ ∀ a b : ℕ, Nat.gcd (a + b + 1) (m * f.eval a + n * f.eval b) > 1) :
    (m, n) = (1, 1) := by 
  rcases h with ⟨f, hfdeg, hf⟩
  -- Choose a = 0, b = 0
  have h1 := hf 0 0
  -- Calculate gcd(1, m*f(0) + n*f(0)) > 1
  norm_num at h1 
  all_goals linarith