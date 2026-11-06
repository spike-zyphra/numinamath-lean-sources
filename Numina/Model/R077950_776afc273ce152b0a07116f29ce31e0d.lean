import Mathlib

def S : ℕ → ℕ
| n => (Nat.digits 10 n).sum

theorem number_theory_247962 :
    ∑ i in Finset.range 2017, (-1 : ℤ)^i * S (i + 1) = 1009 := by
  native_decide