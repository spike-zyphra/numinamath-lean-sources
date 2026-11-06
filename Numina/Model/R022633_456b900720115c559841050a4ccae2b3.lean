import Mathlib

theorem number_theory_64241 (n k : ℤ) (h₀ : 0 < n) (h₁ : 0 < k)
    (h₂ : IsCoprime n 30) :
    ∃ a b, IsCoprime a n ∧ IsCoprime b n ∧
      ∃ m : ℤ, (a ^ 2 - b ^ 2 + k) / n = m := by
  refine' ⟨1, 1, ?_⟩
  constructor
  · -- Show that 1 is coprime to n
    show IsCoprime 1 n
    simp [Int.isCoprime_iff_gcd_eq_one]
  constructor
  · -- Show that 1 is coprime to n
    show IsCoprime 1 n
    simp [Int.isCoprime_iff_gcd_eq_one]
  · -- Show the existence of m
    refine' ⟨(1 ^ 2 - (1 : ℤ) ^ 2 + k) / n, by omega⟩