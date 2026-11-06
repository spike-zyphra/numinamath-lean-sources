import Mathlib

theorem algebra_111255 {a b c : ℝ} (ha : a ≠ -b) (hb : b ≠ -c) (hc : a ≠ -c)
    (h : ∃ d, 1 / (a + b) = 1 / (a + c) + d ∧ 1 / (a + c) = 1 / (b + c) + d) :
    ∃ d, a ^ 2 = b ^ 2 + d ∧ b ^ 2 = c ^ 2 + d := by
  rcases h with ⟨d, h1, h2⟩
  have hb1 : a + b ≠ 0 := by
    intro h
    apply ha
    linarith
  have hb2 : a + c ≠ 0 := by
    intro h
    apply hc
    linarith
  have hb3 : b + c ≠ 0 := by
    intro h
    apply hb
    linarith
  have eq3 : 1 / (a + b) + 1 / (b + c) = 2 * (1 / (a + c)) := by 
    have eq4 : 1 / (a + b) - 1 / (a + c) = d := by linarith
    have eq5 : 1 / (a + c) - 1 / (b + c) = d := by linarith
    linarith
  have eq4 : (a + c) * (b + c) + (a + b) * (a + c) = 2 * (a + b) * (b + c) := by
    have eq3' : 1 / (a + b) + 1 / (b + c) = 2 * (1 / (a + c)) := eq3
    field_simp [(show a + b ≠ 0 by assumption), (show a + c ≠ 0 by assumption), (show b + c ≠ 0 by assumption)] at eq3' ⊢
    ring_nf at eq3' ⊢
    <;> nlinarith
  have eq5 : a ^ 2 + c ^ 2 = 2 * b ^ 2 := by
    nlinarith
  use b ^ 2 - c ^ 2
  constructor
  · -- Show a ^ 2 = b ^ 2 + d
    nlinarith [eq5]
  · -- Show b ^ 2 = c ^ 2 + d
    nlinarith [eq5]