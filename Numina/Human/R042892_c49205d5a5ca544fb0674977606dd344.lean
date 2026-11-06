import Mathlib

theorem number_theory_45148 : Set.Infinite {k : ℕ | ∃ n, 3^n ≡ k [MOD n]} := by
  have h : {k : ℕ | ∃ n, 3^n ≡ k [MOD n]} = Set.univ := by
    ext k
    simp [Nat.ModEq]
    use 1
    <;> omega
  rw [h]
  exact Set.infinite_univ
  