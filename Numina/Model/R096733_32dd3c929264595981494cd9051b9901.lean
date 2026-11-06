import Mathlib
import Aesop

open Nat
theorem AMC_Number_Theory_1138_1 (a b c:ℕ) (habc:a*b*c=2002): 38≤a+b+c:=by
--We have the length of the three dimensions a,b,c are all positive.
  have apos:0<a:=by
    contrapose! habc
    simp only [nonpos_iff_eq_zero] at habc;rw[habc,zero_mul,zero_mul]
    simp only [ne_eq, OfNat.zero_ne_ofNat, not_false_eq_true]
  have bpos:0<b:=by
    contrapose! habc
    simp only [nonpos_iff_eq_zero] at habc;rw[habc,mul_zero,zero_mul]
    simp only [ne_eq, OfNat.zero_ne_ofNat, not_false_eq_true]
  have cpos:0<c:=by
    contrapose! habc
    simp only [nonpos_iff_eq_zero] at habc;rw[habc,mul_zero]
    simp only [ne_eq, OfNat.zero_ne_ofNat, not_false_eq_true]
--Because the volune and dimensions are all integers, we know that each dimension divides the volume。
  have advd2002:a∈  divisors 2002:=by
    simp;use b*c;rw[←mul_assoc,habc]
  have bdvd2002:b∈  divisors 2002:=by
    simp;use a*c;rw[mul_comm,mul_assoc,mul_comm c,←mul_assoc,habc]
  have cdvd2002:c∈  divisors 2002:=by
    simp;use a*b;rw[mul_comm,habc]
--If a single dimension is greater than 37, it's done.
  by_cases ha:38≤a
  linarith
  by_cases hb:38≤b
  linarith
  by_cases hc:38≤c
  linarith
--We use aux to simplify the discussion.
  simp at ha hb hc
  have aux (x:ℕ) (xpos:0<x) (xub:x<38) (xdvd2002:x ∈ divisors 2002):x =1∨x=2∨x=7∨x=11∨x=13∨x=14∨x=22∨x=26:=by
    simp at xdvd2002
    interval_cases x
    all_goals
      revert xdvd2002
      norm_num
--Now a,b,c all lie in a set of 8 elements, we consider the result case by case.
  replace ha:=aux a apos ha advd2002
  replace hb:=aux b bpos hb bdvd2002
  replace hc:=aux c cpos hc cdvd2002
  rcases ha with ha|ha|ha|ha|ha|ha|ha|ha
  all_goals
    rcases hb with hb|hb|hb|hb|hb|hb|hb|hb
    all_goals
      rcases hc with hc|hc|hc|hc|hc|hc|hc|hc
      all_goals
        revert habc
        rw[ha,hb,hc]
        norm_num
theorem AMC_Number_Theory_1138_2 :∃ a b c, a*b*c=2002∧a+b+c=38:=by
  exact ⟨11, 13, 14, by norm_num, by norm_num⟩