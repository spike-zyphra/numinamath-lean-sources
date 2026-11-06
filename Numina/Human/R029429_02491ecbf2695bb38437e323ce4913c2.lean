import Mathlib

/- Using Wilson's theorem, find the least positive residue of \(8 \cdot 9 \cdot 10 \cdot 11 \cdot 12 \cdot 13\) modulo 7.-/
theorem number_theory_4781 [Fact (Nat.Prime 7)] : 8*9*10*11*12*13 = (6 : ZMod 7) :=
  -- exact `ZMod.wilsons_lemma` in Mathlib
  ZMod.wilsons_lemma 7
