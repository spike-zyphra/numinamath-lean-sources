import Mathlib

theorem number_theory_4654 (a b m n : ℤ) (ha : 0 < m) (hb : 0 < n) (hc : n ∣ m) (hd : a ≡ b [ZMOD m]) : a ≡ b [ZMOD n] := by 
  exact Int.ModEq.of_dvd hc hd