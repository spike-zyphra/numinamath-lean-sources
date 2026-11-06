import Mathlib

theorem number_theory_281007 (a b : ℕ) (ha : a < 10) (hb : b < 10)
    (h1 : 18600 + 10 * a + b ≡ 2 [MOD 3]) (h2 : 18600 + 10 * a + b ≡ 3 [MOD 5])
    (h3 : 18600 + 10 * a + b ≡ 0 [MOD 11]) :
    a = 2 ∧ b = 3 := by 
  norm_num [Nat.ModEq] at h1 h2 h3 
  interval_cases a <;> interval_cases b 
    <;> omega