import Mathlib

open Nat

/-
BaseChange theorem: Converts a number from base 16 to base 8 and establishes relationships between the digits
This theorem takes a number N represented in base 16 with specific constraints and shows how its digits
relate to its representation in base 8. Specifically, N is given as a polynomial in 16 with coefficients x and y,
and the theorem proves the exact correspondence between these coefficients and the digits a, b, c, d, e of N in base 8.
-/
theorem BaseChange (x y N:ℕ)(a b c d e: ℕ)(kx_g: x≥1)(kx_l: x≤ 7)(ky_l:y≤15)(kn: N=16^3*x+16^2*y+16*x+y)
(ha: a≤7)(hb: b≤7)(hc: c≤7)(hd: d≤7)(he: e≤7)(kn': N=a*8^4+b*8^3+c*8^2+d*8+e)
:a=x∧b=y/2∧c=(4*y+(16*x+y)/64)%8∧d=(2*x+y/8)%8∧e=y%8:=by
  -- Prove e = y mod 8 by showing both representations of N mod 8 are equal
  have E: e=y%8 := by
    have Mod8: N%8=y%8:=by
      -- Factor out 8 from the 16-based expression to compute mod 8
      have u: 16 ^ 3 * x + 16 ^ 2 * y + 16 * x=(2*16 ^ 2 * x + 2*16  * y + 2 * x)*8:=by ring
      rw[kn,u,add_mod,mul_mod_left,zero_add,mod_mod]
    -- Compute N mod 8 from the 8-based expression
    have Mod'8 : N%8=e:=by
      have v: a * 8 ^ 4 + b * 8 ^ 3 + c * 8 ^ 2 + d * 8=(a * 8 ^ 3 + b * 8 ^ 2 + c * 8  + d )*8:=by ring
      rw[kn',add_mod,v,mul_mod_left,zero_add,mod_mod,mod_eq_iff_lt]
      linarith
      decide
    linarith
  -- Relate the two representations by removing the mod 8 term
  have M: 2*16 ^ 2 * x + 2*16  * y + 2 * x +  (y / 8) = (a * 8 ^ 2 + b * 8  + c )* 8  + d:=by
    have hn:  16 ^ 3 * x + 16 ^ 2 * y + 16 * x + y - y%8=a * 8 ^ 4 + b * 8 ^ 3 + c * 8 ^ 2 + d * 8+y%8 -y%8:= by
      rw[←kn,←E,kn']
    rw[add_sub_self_right] at hn
    -- Use mod-add-div identity for y
    have hy: y%8+ 8*(y/8)=y:= mod_add_div y 8
    nth_rw 2 [←hy] at hn
    rw[add_comm (y%8),←add_assoc] at hn
    -- Simplify the left-hand side by canceling y%8 terms
    have r: 16 ^ 3 * x + 16 ^ 2 * y + 16 * x + 8 * (y / 8) + y % 8 - y % 8 = 16 ^ 3 * x + 16 ^ 2 * y + 16 * x + 8 * (y / 8):=by omega
    rw[r] at hn
    omega
  -- Prove d = (2x + y/8) mod 8 by taking mod 8 of both sides of M
  have D: d=(2*x+y/8)%8:= by
    have Mod8:( 2 * 16 ^ 2 * x + 2 * 16 * y + 2 * x + y / 8 )%8=((a * 8 ^ 2 + b * 8  + c )* 8  + d)%8:= by rw[M]
    -- Factor out 8 from the 16-based coefficients
    have cal: 2 * 16 ^ 2 * x + 2 * 16 * y=(64 * x + 4 * y)*8:= by omega
    rw[cal,add_assoc,add_mod,mul_mod_left,zero_add,mod_mod] at Mod8
    -- Factor out 8 from the 8-based coefficients
    have cal':a * 8 ^ 2 + b * 8=(a * 8  + b )*8:=by omega
    rw[cal'] at Mod8
    nth_rw 2[add_mod] at Mod8
    rw[mul_mod_left,zero_add,mod_mod] at Mod8
    symm
    rw[Mod8,mod_eq_of_lt]
    linarith
  -- Rewrite M using the expression for d
  have K: 2 * 16 ^ 2 * x + 2 * 16 * y + (2 * x + y / 8) = (a * 8 ^ 2 + b * 8 + c) * 8 + (2 * x + y / 8) % 8:=by rw[←add_assoc,M,D]
  -- Apply mod-add-div identity to (2x + y/8)
  have div8: (2 * x + y / 8)%8+8*((2 * x + y / 8)/8)=2 * x + y / 8:=by rw[mod_add_div]
  nth_rw 1 [←div8] at K
  simp at K
  -- Simplify both sides by canceling the 8 factor
  have K':(64 * x + 4 * y +((2 * x + y / 8) / 8))*8 = (a * 64 + b * 8 + c) * 8 :=by linarith
  simp at K'
  have K0: 8 * x*8 + 4 * y + (2 * x + y / 8) / 8 = (a * 8 + b) * 8 + c:= by linarith
  -- Key equality relating (16x + y)/64 to (2x + y/8)/8
  have Key: (2 * x + y / 8) / 8= (16 * x + y) / 64:=by
      -- Case analysis on y < 8 and y ≥ 8, x < 4 and x ≥ 4
      by_cases Y: y<8
      have div: y/8=0:=by
        rw[div_eq_of_lt]
        exact Y
      rw[div,add_zero]
      by_cases X:x<4
      have div: 2*x/8=0:= by
        rw[div_eq_of_lt]
        linarith
      rw[div,div_eq_of_lt]
      have X:x≤3:=by
        apply Nat.lt_add_one_iff.mp
        simp
        exact X
      linarith
      simp at X
      have div: 2*x/8=1:=by
        have l: 0 < 8 ∧ 8 ≤ 2 * x:=by
          omega
        rw[Nat.div_eq]
        simp[l]
        have L: 2*x≤14:=by linarith
        have L': 2*x-8≤ 14-8:=by
          simp
          exact L
        linarith
      rw[div]
      have l: 0 < 64 ∧ 64 ≤ 16 * x + y :=by
        constructor
        decide
        linarith
      rw[Nat.div_eq]
      simp[l]
      have L:16*x+y≤ 16*7+8:= by linarith
      have L':16*x+y-64≤ 16*7+8-64:= by
        simp
        exact L
      linarith
      simp at Y
      have div: y/8=1:=by
        have l:0 < 8 ∧ 8 ≤ y:=by
          constructor
          decide
          exact Y
        rw[Nat.div_eq]
        simp[l]
        have sub: y-8≤ 15-8:=by
          simp
          exact ky_l
        have tr: 15-8<8:=by
          decide
        apply gt_of_gt_of_ge tr
        exact sub
      rw[div]
      by_cases Rx: x≥4
      have div: (2 * x + 1) / 8=1:=by
        have l:0 < 8 ∧ 8 ≤ 2 * x + 1:=by
          omega
        rw[Nat.div_eq]
        simp[l]
        omega
      rw[div]
      rw[Nat.div_eq]
      have l:0 < 64 ∧ 64 ≤ 16 * x + y :=by
        omega
      simp[l]
      omega
      simp at Rx
      have Rx:x≤ 3:=by
        apply Nat.lt_add_one_iff.mp
        simp
        exact Rx
      have div:(2*x+1)/8=0:=by
        rw[div_eq_of_lt]
        omega
      rw[div]
      symm
      rw[div_eq_of_lt]
      omega
  -- Prove c = (4y + (16x + y)/64) mod 8 using K0 and Key
  have C:c=(4*y+(16*x+y)/64)%8:=by
    have Mod8: (8 * x*8 + 4 * y + (2 * x + y / 8) / 8)%8=((a * 8 + b) * 8 + c)%8:=by rw[K0]
    rw[add_assoc,add_mod,mul_mod_left,zero_add,mod_mod] at Mod8
    nth_rw 2[add_mod] at Mod8
    rw[add_mod,mul_mod_left,zero_add,mod_mod,←add_mod] at Mod8
    rw[Key] at Mod8
    rw[Mod8,mod_eq_of_lt]
    omega
  -- Construct the final proof by combining all parts
  constructor
  swap
  constructor
  swap
  exact ⟨C,D,E⟩
  -- Further simplification to prove a = x by canceling common terms
  rw[Key,C] at K0
  have d:(4*y+(16 * x + y)/64)%8+8*((4*y+(16 * x + y)/64)/8)=(4*y+(16 * x + y)/64) :=by
    rw[mod_add_div]
  nth_rw 1 [←d] at K0
  rw[add_assoc,add_comm ((4*y+(16 * x + y)/64) % 8),←add_assoc,mul_comm,←mul_assoc,add_assoc (8*8*x),add_comm (4*y),←add_assoc,mul_assoc] at K0
  rw[add_mod,mul_mod_right,zero_add,mod_mod,mod_mod] at K0
  have d:((16 * x + y)/64+4*y)%8+8*(((16 * x + y)/64+4*y)/8)=((16 * x + y)/64+4*y) :=by
    rw[mod_add_div]
  rw[add_assoc] at K0
  nth_rw 1 [←d] at K0
  rw[←add_assoc] at K0
  have Ks: 8 * (8 * x) + ((16 * x + y) / 64 + 4 * y) % 8 + 8 * (((16 * x + y) / 64 + 4 * y) / 8)-((16 * x + y) / 64 + 4 * y) % 8 =
  (a * 8 + b) * 8 + ((16 * x + y) / 64 + 4 * y) % 8-((16 * x + y) / 64 + 4 * y) % 8:=by
    rw[K0]
  simp at Ks
  rw[add_assoc,add_comm (((16 * x + y) / 64 + 4 * y) % 8),add_mod,←add_assoc] at Ks
  simp at Ks
  rw[←mul_add,mul_comm] at Ks
  apply Nat.mul_right_cancel at Ks
  have s: (8 * x + ((16 * x + y) / 64 + 4 * y) / 8)%8 = (a * 8 + b)%8:=by rw[Ks]
  rw[add_mod,mul_mod_right,zero_add,mod_mod,add_mod,mul_mod_left,zero_add,mod_mod] at s
  -- Prove the remaining term relates to b = y/2
  have L:((16 * x + y) / 64 + 4 * y) / 8 % 8=y/2:=by
    have le:(16 * x + y) / 64≤1:=by
      rw[Nat.div_eq]
      by_cases wh:0 < 64 ∧ 64 ≤ 16 * x + y
      simp[wh]
      omega
      simp at wh
      simp[wh]
      split_ifs with h
      simp
      omega
      decide
    by_cases r0:(16 * x + y) / 64=0
    rw[r0,zero_add]
    have :8=4*2:=by decide
    nth_rw 1[this]
    rw [Nat.mul_div_mul_left]
    rw[mod_eq_iff_lt]
    omega
    decide
    decide
    interval_cases (16 * x + y) / 64
    contradiction
    have fl: y%2+2*(y/2)=y:=by
      apply mod_add_div
    nth_rw 1 [←fl]
    rw[mul_add,←mul_assoc,←add_assoc 1]
    simp
    rw[Nat.add_mul_div_left]
    have j: (1 + 4 * (y % 2)) / 8=0 :=by
      rw[div_eq_of_lt]
      have l:(y % 2)<2:=by
        apply Nat.mod_lt
        decide
      apply Nat.lt_add_one_iff.mp at l
      omega
    rw[j,zero_add,mod_eq_iff_lt]
    omega
    decide
    omega
  rw[L]at s
  rw[s]
  symm
  rw[mod_eq_iff_lt]
  omega
  decide
  omega
  -- Final step: prove a = x by dividing both representations by 8^4
  have div:( 16 ^ 3 * x + 16 ^ 2 * y + 16 * x + y)/(8^4)=(a * 8 ^ 4 + b * 8 ^ 3 + c * 8 ^ 2 + d * 8 + e)/(8^4):=by
    rw[←kn,kn']
  rw[add_assoc (16 ^ 3 * x)] at div
  have eq: 16^3=8^4:=by norm_num
  rw[eq] at div
  rw[add_assoc (8 ^ 4 * x),add_comm (8 ^ 4 * x),Nat.add_mul_div_left]at div
  have eq:(16 ^ 2 * y + 16 * x + y) / 8 ^ 4=0:=by
    apply Nat.div_eq_of_lt
    omega
  rw[eq,zero_add] at div
  rw[add_assoc (a * 8 ^ 4),add_assoc (a * 8 ^ 4),add_assoc (a * 8 ^ 4),add_comm (a * 8 ^ 4),Nat.add_mul_div_right]at div
  have eq:(b * 8 ^ 3 + c * 8 ^ 2 + d * 8 + e) / 8 ^ 4 =0:=by
    apply Nat.div_eq_of_lt
    omega
  rw[eq,zero_add] at div
  symm
  exact div
  decide
  decide
