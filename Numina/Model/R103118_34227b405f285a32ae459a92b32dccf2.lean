import Mathlib

theorem number_theory_39522 (k : ℕ) (hk : 1 < k) (p : ℕ) (hp : Nat.Prime p)
    (hpk : p = 6 * k + 1) (m : ℕ) (hm : m = 2 ^ p - 1) :
    ∃ x : ℤ, (2 ^ (m - 1) - 1) / (127 * m) = x := by 
  refine ⟨(2 ^ (m - 1) - 1) / (127 * m), by omega⟩