import Mathlib

/-Let a,b and c be digits with $a\neq 0$. The three-digit integer abc lies one third of the way from the square of a positive integer to the square of the next larger integer. The integer acb lies two thirds of the way between the same two squares. What is a+b+c?
(A) 10(B) 13(C) 16(D) 18(E) 21-/
open Nat
theorem AMC_Number_theory_98355 (a b c : ℕ) (_ : a ≠ 0) (ha:0≤a∧a≤9) (hb:0≤b∧b≤9) (hc:0≤c∧c≤9)
(h : ∃ n : ℕ, 0 < n ∧ (100 * a + 10 * b + c) = (n ^ 2) + ((1:ℚ) / 3) * ((n + 1) ^ 2 - (n ^ 2)) ∧ (100 * a + 10 * c + b) = (n ^ 2) + ((2:ℚ) / 3) * ((n + 1) ^ 2 - (n ^ 2))) :
a + b + c = 16 := by
  rcases h with ⟨n,npos,hn1,hn2⟩
  rcases ha with ⟨anonneg,ale9⟩
  rcases hb with ⟨bnonneg,ble9⟩
  rcases hc with ⟨cnonneg,cle9⟩
--First, we know that the square of n is not greater than (abc)_{10}, thus also no greater than 999.
  have nsqle:n^2≤(100 * a + 10 * b + c):=by
    rw[←@Nat.cast_le Rat]
    norm_num
    rw[hn1]
    ring_nf
    simp only [one_div, le_add_iff_nonneg_left]
    apply add_nonneg
    norm_num
    norm_num
  have nsqle999:n^2≤999:=by
    apply le_trans nsqle
    linarith
--Use hn2 sub hn1, we know that 27*(c-b)=2*n+1.
  have csubb:(1:ℚ)/3*((n+1)^2-n^2)=9*(c-b):=by linarith
  field_simp at csubb
  rw[mul_comm _ 3,←mul_assoc,show (3:ℚ)*9=27 by norm_num] at csubb
--Because n is a natural number, we know that b is smaller than c.
  have bltc:b<c:=by
    rw[←@Nat.cast_lt Rat,←sub_pos]
    rw[←(mul_pos_iff_of_pos_right (show 0<(27:Rat) by norm_num))]
    rw[mul_comm,←csubb]
    ring_nf
    norm_cast
    linarith
  rw[←Nat.cast_sub (by linarith)] at csubb
  ring_nf at csubb
  norm_cast at csubb
--As 2*n+1 is odd, we know that (c-b) is also odd.
  have csubbodd:Odd (c-b):=by
    have :Odd (1+n*2):=by simp only [even_two, Even.mul_left, Even.one_add]
    rw[csubb] at this
    apply Odd.of_mul_left this
--We prove that if c-b is greater than 2, then n^2 is greater than 1000, which yields a contradiction.
  by_cases hcb:c-b>2
  · have :81≤(c-b)*27 := by linarith
    rw[←csubb] at this
    have nge40:40≤n:=by linarith
    apply mul_le_mul nge40 at nge40
    simp only [_root_.zero_le, reduceMul, forall_const] at nge40
    linarith
--We prove that c-b=1 as it is odd and smaller than 3.
  · replace hcb:c-b=1:=by
      interval_cases (c-b)
      · linarith
      · rfl
      · contrapose! csubbodd
        simp only [not_odd_iff_even, even_two]
    rw[hcb] at csubb
--Substitute the value of c-b, we know that n=13.
    have neq:n=13 := by linarith
    rw[neq] at hn1 hn2
    norm_num at hn1 hn2
    norm_cast at hn1 hn2
--Because (abc)_{10}=178, we know that a=1,b=7 and c=8.
    have ha:a=1:=by
      apply Linarith.eq_of_not_lt_of_not_gt
      · linarith
      · linarith
    have bceq:b=7∧c=8:=by
      constructor <;> linarith
--The result follows.
    rw[ha,bceq.1,bceq.2]