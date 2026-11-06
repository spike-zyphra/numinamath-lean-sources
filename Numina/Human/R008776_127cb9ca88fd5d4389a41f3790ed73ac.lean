import Mathlib

--Determine the last two digits of $$17^{17}$$, written in base 10.

theorem Number_theory_608434 : (17^17) % 100 = 77 :=
  by 
    -- using `norm_num` to compute powers and modulus efficiently,
    norm_num [Nat.ModEq, Nat.mod_eq_of_lt]