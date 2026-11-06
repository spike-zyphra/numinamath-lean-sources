import Mathlib
open Real

/-What is the largest positive integer n for which there is a unique integer k such that
8/15< n/(n+k)<7/13?-/

theorem AIME_Inequalities_52211 {n : Nat} (_ : n > 0) (hn:
(∃! k : Int, (n:Rat) / (n + k) < 7 / 13 ∧ 8 / 15 < (n:Rat) / (n + k))):n≤112 ∧ (∃! k:Int, (112:Rat)/(112+k)<7/13∧8/15<(112:Rat)/(112+k)) := by
--We prove that it must be no greater than 112 and then prove that 112 satisfies the property.
--We prove two lemmas to help linarith.
  have aux1 (a:Rat):a<Int.floor a+2:=by
    apply lt_trans (Int.lt_floor_add_one a) (by linarith)
  have aux2 (a b:Rat) (hab:2<b-a):Int.floor a+2<b:=by linarith[Int.floor_le a]
  constructor
--First, let's prove 112≤n
  · rcases hn with ⟨k,⟨⟨ha,hb⟩,kuni⟩⟩
    have hpos:0<(n:Rat) +k:=by
      replace hb :0<n/((n:Rat)+k):=by linarith
      rw[div_pos_iff] at hb
      rcases hb with ⟨_,hb⟩|⟨_,hb⟩
      linarith;linarith
--We simplify the condition ha hb.
    rw[div_lt_div_iff hpos (by norm_num)] at ha
    rw[div_lt_div_iff (by norm_num) hpos] at hb
    replace ha:6*(n:Rat)/7<k:=by linarith
    replace hb:(k:Rat)<7*n/8:=by linarith
--Now we get the actual bound for k. We prove that if the difference of two rational numbers is greater than 2, then there are at least two different integers between them.
    have aux3(a b:Rat):(2<b-a)→∃ (k1 k2: Int),k1<k2∧ a<k1∧a<k2∧k1<b∧k2<b:=by
      intro hab
      use (Int.floor a)+1, (Int.floor a)+2
      simp only [Int.cast_add,Int.cast_add, Int.cast_one, Int.lt_floor_add_one,Int.cast_ofNat,Int.cast_ofNat,true_and]
      split_ands
      · linarith
      · apply aux1
      · linarith[aux2 a b hab]
      · apply (aux2 _ _ hab)
--We prove that we only need to prove the gap between 7n/8 and 6n/7 is less or equal to 2.
    suffices h:7*(n:Rat)/8-6*n/7≤2 by
      ring_nf at h;field_simp at h
      rw[←(@Nat.cast_le Rat)]
      rw[div_le_iff] at h
      norm_num at h
      simp only [Nat.cast_ofNat, Nat.cast_le_ofNat, h]
      norm_num
--Now,their gap can be no greater than 2, otherwise we prove that it will contradicts to the uniqueness of k.
    contrapose! kuni
    rcases (aux3 _ _ kuni) with ⟨k1,k2,hk,h1,h2,h3,h4⟩
--We have k1 and k2,with the same property as k does, and they are different, then at least one of them is not k.
    by_cases heq:k=k1
    · use k2
      split_ands
      · rw[div_lt_div_iff ]
        linarith;linarith;norm_num;
      · rw[div_lt_div_iff]
        linarith;norm_num;linarith;
      · linarith
    · use k1
      split_ands
      · rw[div_lt_div_iff ]
        linarith;linarith;norm_num;
      · rw[div_lt_div_iff]
        linarith;norm_num;linarith
      · push_neg at heq
        symm;exact heq
--On the other hand, we prove that when n=112, the unique k=97 exists.
  · use 97
    constructor
--97 has this property by norm_num.
    · norm_num
--Now we show that 97 is unique by the discreteness of integers.
    · intro y ⟨ya,yb⟩
      suffices h:96<y∧y<98 by
        rcases h with ⟨h1,h2⟩
        linarith
      rw[←(@Int.cast_lt Rat),←(@Int.cast_lt Rat)]
      have hpos:0<112+(y:Rat):=by
        replace yb :0<112/(112+(y:Rat)):=by linarith
        rw[div_pos_iff] at yb;norm_num at yb;exact yb
      rw[div_lt_div_iff hpos (by norm_num)] at ya
      rw[div_lt_div_iff (by norm_num) hpos] at yb
      ring_nf at ya yb
      simp only [Int.cast_ofNat]
      constructor
      · linarith
      · linarith