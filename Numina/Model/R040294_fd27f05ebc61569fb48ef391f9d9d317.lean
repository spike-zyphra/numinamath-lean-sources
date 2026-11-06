import Mathlib

theorem algebra_175483 {a b c : ℝ} (hab : a * b ≠ 1) (hbc : b * c ≠ 1) (hac : a * c ≠ -1) :
  let E := (a + b) / (1 - a * b)
  let M := (b + c) / (b * c - 1)
  let H := (c - a) / (1 + a * c)
  E + M + H = E * M * H := by
  have ha1 : 1 - a * b ≠ 0 := by
    intro h'
    apply hab
    linarith
  have ha2 : b * c - 1 ≠ 0 := by
    intro h'
    apply hbc
    linarith
  have ha3 : 1 + a * c ≠ 0 := by
    intro h'
    apply hac
    linarith
  field_simp [ha1, ha2, ha3]
  <;> ring