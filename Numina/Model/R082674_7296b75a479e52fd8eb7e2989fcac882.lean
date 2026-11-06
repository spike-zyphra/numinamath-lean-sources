import Mathlib

theorem algebra_4944 {a b c d : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hd : d ≠ 0) (h1 : a * 7 + b * 19 ≡ 1 [ZMOD 26]) (h2 : a * 19 + b * 7 ≡ 2 [ZMOD 26])
    (h3 : c * 7 + d * 19 ≡ 2 [ZMOD 26]) (h4 : c * 19 + d * 7 ≡ 1 [ZMOD 26]) :
    a = 3 ∧ b = 24 ∧ c = 24 ∧ d = 25 := by
  norm_num [Int.ModEq] at h1 h2 h3 h4
  have ha3 : a = 3 := by
    omega
  have hb24 : b = 24 := by
    omega
  have hc24 : c = 24 := by
    omega
  have hd25 : d = 25 := by
    omega
  exact ⟨ha3, hb24, hc24, hd25⟩