import Mathlib

theorem number_theory_183 (day : ℕ) (h : 0 < day) (h1 : 10 + day ≡ 0 [MOD 7]) :
    1000000 + day ≡ 5 [MOD 7] := by 
  norm_num [Nat.ModEq] at h1 ⊢
  omega