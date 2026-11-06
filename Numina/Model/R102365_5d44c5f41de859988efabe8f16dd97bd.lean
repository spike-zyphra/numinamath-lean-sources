import Mathlib

theorem algebra_96107 (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (h : ∀ x : ℤ, (1 + x ^ (m * n) + ∑ i ∈ Finset.range (m * n), x ^ i) % (1 + x + ∑ i ∈ Finset.range m, x ^ i) = 0) :
    Nat.gcd 1 n = 1 := by 
  simp