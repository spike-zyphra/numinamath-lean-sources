import Mathlib

theorem number_theory_15246 (a b c : ℕ) (ha : a < 7) (hb : b < 7) (hc : c < 7)
    (_ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h1 : a * b * c ≡ 1 [MOD 7]) (h2 : 5 * c ≡ 2 [MOD 7]) (h3 : 6 * b ≡ 3 + b [MOD 7]) :
    (a + b + c) % 7 = 4 := by
  norm_num [Nat.ModEq] at h1 h2 h3 ⊢
  have hc6 : c = 6 := by
    interval_cases c <;> omega
  have hb2 : b = 2 := by
    interval_cases b <;> omega
  have ha3 : a = 3 := by
    rw [hb2, hc6] at h1
    interval_cases a <;> omega
  calc
    (a + b + c) % 7 = (3 + 2 + 6) % 7 := by rw [ha3, hb2, hc6]
    _ = 11 % 7 := by norm_num
    _ = 4 := by norm_num