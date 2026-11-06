import Mathlib

theorem algebra_176722 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : 1 / a = 1 / b + 10 / 24) (h2 : 1 / a = 1 / c + 6 / 24)
    (h3 : 9 / a + 10 / b = 10 / c) :
    1 / a = 20 / 24 ∧ 1 / b = 30 / 24 ∧ 1 / c = 24 / 24 := by 
  constructor
  · -- We need to prove 1 / a = 20 / 24.
    field_simp at h1 h2 h3 ⊢
    <;> nlinarith
  constructor
  · -- We need to prove 1 / b = 30 / 24.
    field_simp at h1 h2 h3 ⊢
    <;> nlinarith
  · -- We need to prove 1 / c = 24 / 24.
    field_simp at h1 h2 h3 ⊢
    <;> nlinarith