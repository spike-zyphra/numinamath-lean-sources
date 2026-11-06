import Mathlib

theorem number_theory_6889 (n : ℕ) (hn : 2 ≤ n) (b : Fin n → ℕ)
    (a : ℕ) (ha : 0 < a) (h : ∀ i, 0 < b i) (h1 : ∀ i, Nat.gcd a (b i) = 1) :
    Nat.gcd a (∏ i, b i) = 1 := by

  have h2 : ∀ i : Fin n, Nat.Coprime a (b i) := by 
    intro i
    have h3 : Nat.gcd a (b i) = 1 := h1 i
    rw [Nat.coprime_iff_gcd_eq_one] 
    exact h3

  have h3 : Nat.Coprime a (∏ i : Fin n, b i) := by 
    apply Nat.Coprime.prod_right 
    intro i hi
    exact h2 i

  rw [Nat.coprime_iff_gcd_eq_one] at h3 
  exact h3