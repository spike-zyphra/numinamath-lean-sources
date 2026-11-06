import Mathlib

/-Let m be the smallest integer whose cube root is of the form n+r where n is a positive integer and r is a positive real number less than 1/1000. Find n.-/
theorem AIME_Number_Theory_95085 (m:Int) (n:Nat) (r:Real) (npos:0<n) (rpos:0<r) (hr:r<1/1000)(hmn:m=(n+r)^3):(19≤n)∧(∃(m:Int) (r:Real),0<r∧r<1/1000 ∧ m=(19+r)^3):=by
--We prove that such n must be no less than 19, and for n=19, there are such n, then since 19 is the minimal for n, it gives the minimal m.
  constructor
  swap
--We prove that n=19 satisfies the property.
  · use 19^3+1, ((19:Real)^(3:Real)+1)^((1:Real)/3)-19
    split_ands
    · rw[sub_pos,one_div,Real.lt_rpow_inv_iff_of_pos]
      norm_num;norm_num;norm_num;norm_num
    · rw[sub_lt_iff_lt_add,one_div,Real.rpow_inv_lt_iff_of_pos]
      norm_num;norm_num;norm_num;norm_num
    · rw[one_div,←Real.rpow_natCast]
      norm_num
      simp only [one_div, Nat.ofNat_nonneg, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,Real.rpow_inv_rpow]
--We prove that such m exists implies n>18.
  · have mpos:0<m:=by rw[←(@Int.cast_lt Real),hmn];field_simp
    have n3ltm:n^3<m:=by
      rw[←(@Int.cast_lt Real),hmn]
      simp only [Int.cast_pow, Int.cast_natCast]
      apply pow_lt_pow_left (by linarith)
      norm_cast;linarith;norm_num
--By the discretness of integers, 1≤m-n^3
    have diff:1≤m-n^3:=by linarith[n3ltm]
    rw[←(@Int.cast_le Real),Int.cast_sub,hmn] at diff
    norm_cast at diff
--We see that the gap between (n+1/1000)^3 and n^3 is greater than 1.
    replace diff:1<((n:Real)+1/1000)^3-n^3:=by
      apply lt_of_le_of_lt diff
      simp only [Nat.cast_pow, one_div, sub_lt_sub_iff_right]
      apply pow_lt_pow_left
      simp only [add_lt_add_iff_left]
      linarith;linarith;norm_num
--We prove for n≤18, no such m exists as there are no integers between n^3 and (n+1/1000)^3
    by_contra! hn
    interval_cases n
    all_goals
      revert diff
      norm_num