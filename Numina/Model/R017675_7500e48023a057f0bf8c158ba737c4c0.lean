import Mathlib

theorem number_theory_15600 : (3^400 ≡ 1 [MOD 1000]) → (3^12000 ≡ 1 [MOD 1000]) := by
  intro h
  have h1 : 3 ^ 12000 % 1000 = 1 := by
    have h2 : (3 ^ 400) % 1000 = 1 := h
    norm_num [Nat.pow_mod, h2]
    all_goals omega
  show 3 ^ 12000 ≡ 1 [MOD 1000]
  norm_num [Nat.ModEq, h1]