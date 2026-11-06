import Mathlib

theorem number_theory_30298 {n : ℕ} (hn : n > 0) (hnsqfree : ∀ m, ¬ ∃ k, m^2 = n * k) :
    ¬∃ x y : ℕ, x > 0 ∧ y > 0 ∧ Nat.Coprime x y ∧ (x + y)^3 ∣ x^n + y^n := by
  by_contra h
  rcases h with ⟨x, y, hx, hy, hco, hdiv⟩
  have h1 := hnsqfree 0 
  have h2 : ∃ k, (0 ^ 2 = n * k) := by
    use 0
    all_goals simp
  contradiction