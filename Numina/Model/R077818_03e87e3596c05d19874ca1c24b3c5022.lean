import Mathlib

theorem algebra_21676 {n : ℕ} (hn : n > 30 ∧ n < 50) :
    ¬∃ k, k > 0 ∧ n % k = 0 ∧ ¬∃ m, m > 0 ∧ (n + 2) % m = 0 := by
  rintro ⟨k, hk₁, hk₂, h⟩
  have h₁ : ∃ m, m > 0 ∧ (n + 2) % m = 0 := by 
    use 1 
    all_goals omega 
  contradiction