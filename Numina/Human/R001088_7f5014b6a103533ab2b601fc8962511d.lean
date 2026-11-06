import Mathlib
open Finset
/- The terms of an arithmetic sequence add to 715. The first term of the sequence is increased by 1, the second term is increased by 3, the third term is increased by 5, and in general, the k-th term is increased by the k-th odd positive integer. The terms of the new sequence add to 836. Find the sum of the first, last, and middle terms of the original sequence. -/
theorem algebra_20395 (a : Nat->Int) (d:Int) (n:Nat) (ha:∀ i, a i = a 0 + d*i) (h₀ : ∑ i ∈ range n, a i= 715) (h₁ : ∑ i ∈ range n, (a i +(i*2+1))= 836) : a 0+ a (n-1)+ a (n/2) = 195 := by
--The sum of the new sequence is $ \sum_{i=0}^{n-1}(a_i+2*i+1)=836$.
  rw[Finset.sum_add_distrib] at h₁
  have sum_odd:∑ i in range n, (i*2+1) = n*n:= by
    rw[Finset.sum_add_distrib,mul_comm]
    simp only [sum_const, card_range, smul_eq_mul, mul_one]
    rw[←sum_mul,sum_range_id_mul_two]
    rw[Nat.mul_sub,mul_one,Nat.sub_add_cancel]
    apply Nat.le_mul_self
--So the $\sum_{i=0}^{n-1}(2*i+1)=836-715=121$
--Thus we have $n^2=121$, which implies $n=11$.
  have neq11:n=11:=by
    rw[←@Nat.cast_inj Int] at sum_odd
    simp only [Nat.cast_sum, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at sum_odd
    rw[sum_odd,h₀] at h₁
    norm_cast at h₁
    nlinarith
--Substitute $n=11$ into the equations.
  rw[neq11] at h₀ h₁ ⊢
  norm_num
--Because $a_n$ is an arithmetic sequence, we have $a_n=a_0+d*(n-1)$ for some $d$.
  have sumcast (n:Nat):∑ i ∈ range n, a i=∑ i∈range n, (a 0 +d*i):=by
    apply sum_congr (by rfl)
    intro i hi
    rw[ha]
--We have $11*a_0+55*d=715$.
  rw[sumcast,sum_add_distrib,sum_const,card_range,←mul_sum] at h₀
  norm_num at h₀
--Because the sequence is an arithmetic sequence, we have $a_0+a_10+a_5=3*a_0+15*d$.
  rw[ha 10,ha 5]
  ring_nf
  rw[←@Int.cast_inj Real] at h₀ ⊢
  simp only [Int.cast_sum, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one] at h₀
  simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat]
--Because $11*a_0+55*d=715$, we have $3*a_0+15*d=3*(715-55*d)/11$.
  linarith