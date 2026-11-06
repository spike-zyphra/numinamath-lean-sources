import Mathlib

theorem number_theory_6856 (x : ℤ) : (1215 * x ≡ 560 [ZMOD 2755]) ↔
    x ≡ 200 [ZMOD 2755] ∨ x ≡ 751 [ZMOD 2755] ∨
    x ≡ 1302 [ZMOD 2755] ∨ x ≡ 1853 [ZMOD 2755] ∨
    x ≡ 2404 [ZMOD 2755] := by
  simp [Int.ModEq]
  <;> omega