import Mathlib

theorem number_theory_73561 (n : ℕ) (hn : 1 < n) :
    ∃ a : Fin n → ℤ, ∀ i j, a i + a j ≡ a i + a i [ZMOD n * (n + 1) / 2] := by 
  use (λ _ => (0 : ℤ))
  intro i j
  simp [Int.ModEq]