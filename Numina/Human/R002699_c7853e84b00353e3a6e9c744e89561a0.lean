import Mathlib
open Nat

/- 34. Find the last 2 digits of

$$

x=19^{17^{15^{3}}}

$$
 -/
theorem number_theory_101587 : 19^(17^(15^13)) ≡ 59 [MOD 100] := by
  set b := 15^13
  -- show that b = 15 (mod φ (φ 100))
  have hb_mod : b = 16 * (b / 16) + 15
  · nth_rw 1 [←Nat.div_add_mod b 16, add_right_inj]
    norm_num
  have h1 : 17^15 ≡ 33 [MOD 40]
  · decide
  -- show a = 17^b = 33 (mod φ 100) using Fermat-Euler
  set a := 17^b with ha
  have h2 : a ≡ 33 [MOD 40]
  · rw [ha, hb_mod, pow_add, pow_mul, ←one_mul 33]
    apply Nat.ModEq.mul _ h1
    rw [←one_pow (b / 16)]
    apply Nat.ModEq.pow
    rw [show 16 = totient 40 by decide]
    exact Nat.ModEq.pow_totient (by norm_num)
  -- conclude using this and another application of Fermat-Euler
  have ha_mod : a = 40 * (a / 40) + 33
  · nth_rw 1 [←Nat.div_add_mod a 40, h2]
  have h3 : 19^33 ≡ 59 [MOD 100]
  · decide
  rw [ha_mod, pow_add, pow_mul, ←one_mul 59]
  apply Nat.ModEq.mul _ h3
  nth_rw 1 [show 40 = totient 100 by decide, ←one_pow (a / 40)]
  apply Nat.ModEq.pow
  exact Nat.ModEq.pow_totient (by norm_num)