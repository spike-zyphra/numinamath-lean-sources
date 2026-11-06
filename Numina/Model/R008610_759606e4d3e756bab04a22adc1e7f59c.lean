import Mathlib

theorem number_theory_16038 (a b c : ℕ) (ha : a < 7) (hb : b < 7) (hc : c < 7)
    (h1 : a + 2 * b + 3 * c ≡ 0 [MOD 7]) (h2 : 2 * a + 3 * b + c ≡ 4 [MOD 7])
    (h3 : 3 * a + b + 2 * c ≡ 4 [MOD 7]) :
    a * b * c ≡ 6 [MOD 7] := by
  simp [Nat.ModEq] at h1 h2 h3 ⊢
  interval_cases a <;> interval_cases b <;> interval_cases c
  <;> omega