import Mathlib

theorem algebra_5307 {a b c : ℤ} (ha : a = 242) (hb : b = 243) (hc : c = 244)
    (h : ∑ i ∈ Finset.range 100, (2 / (3 ^ i)) = a * b / c) :
    a = 242 := by
  exact ha