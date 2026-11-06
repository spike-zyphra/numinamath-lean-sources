import Mathlib

theorem number_theory_291150 (n : ℕ) (hn : 1 ≤ n) (p : Fin n → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (a : Fin (n + 1) → ℕ)
    (ha : ∀ i, ∃ s : Finset (Fin n), a i = ∏ i ∈ s, p i) :
    ∃ t : Finset (Fin (n + 1)), IsSquare (∏ i ∈ t, a i) := by 
  use (∅ : Finset (Fin (n + 1)))
  have h2 : (∏ i ∈ (∅ : Finset (Fin (n + 1))), a i) = 1 := by
    simp
  have h3 : IsSquare (∏ i ∈ (∅ : Finset (Fin (n + 1))), a i) := by 
    rw [h2]
    exact ⟨1, by norm_num⟩
  exact h3