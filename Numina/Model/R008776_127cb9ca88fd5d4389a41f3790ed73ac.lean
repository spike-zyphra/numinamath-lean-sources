import Mathlib

--Determine the last two digits of $$17^{17}$$, written in base 10.

theorem Number_theory_608434 : (17^17) % 100 = 77 :=
  by
    norm_num