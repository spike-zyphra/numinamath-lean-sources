import Mathlib

theorem number_theory_636886 (p : ℕ) (hp : Odd p ∧ Nat.Prime p) (k : ℕ) 
  (hk : k = orderOf (2 : ZMod p)) :
  2 ^ 2006 ≡ 2 ^ (2006 % k) [ZMOD p] := by 
  have h1 : 2 ^ k ≡ 1 [ZMOD p] := by
    rw [hk]
    refine (ZMod.intCast_eq_intCast_iff (2 ^ orderOf 2) 1 p).mp ?_
    norm_num
    exact pow_orderOf_eq_one 2
  have h2 : 2006 = 2006 / k * k + 2006 % k := by 
    exact Eq.symm (Nat.div_add_mod' 2006 k)
  nth_rw 1 [h2]
  rw [pow_add]
  have h3 : 2 ^ (2006 / k * k) ≡ 1 [ZMOD p] := by 
    calc 
      _ ≡ (2 ^ k) ^ (2006 / k) [ZMOD p] := by 
        rw [←pow_mul, mul_comm]
      _ ≡ 1 ^ (2006 / k) [ZMOD p] := by 
        exact Int.ModEq.pow (2006 / k) h1
      _ ≡ 1 [ZMOD p] := by simp
  calc 
    _ ≡ 1 * 2 ^ (2006 % k) [ZMOD p] := by 
      exact Int.ModEq.mul h3 rfl
    _ ≡ 2 ^ (2006 % k) [ZMOD p] := by
      simp