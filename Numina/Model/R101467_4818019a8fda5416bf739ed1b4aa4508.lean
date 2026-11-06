import Mathlib

open Finset

theorem number_theory_4805_1 {p : ℕ} (hp : p.Prime) (a b : ℤ) : (a+b)^p ≡ a^p+b^p [ZMOD p] := by
  haveI : 2 ≤ p := Nat.Prime.two_le hp
  -- To prove that \((a+b)^{p} \equiv a^{p} + b^{p} \mod p\), we start by applying the binomial theorem, which states that:
-- \[
-- (a+b)^{p} = \sum_{k=0}^{p} \binom{p}{k} a^{p-k} b^{k}
-- \]
  rw [add_pow, sum_range_succ]
--   This expands to:
-- \[
-- (a+b)^{p} = a^{p} + b^{p} + \sum_{k=1}^{p-1} \binom{p}{k} a^{p-k} b^{k}
-- \]
  simp
  conv => lhs; lhs; lhs; rw [show p = p - 1 + 1 by omega]
  rw [sum_range_succ']
  simp
  rw [add_assoc, add_comm (b^p)]
  symm
  rw [Int.modEq_iff_dvd, Int.add_sub_cancel]
  apply dvd_sum
  intro i hi
  simp at hi
  apply Dvd.dvd.mul_left
  norm_cast
  -- Now, we know from our earlier result that for \(1 \leq k \leq p-1\), the binomial coefficient \(\binom{p}{k}\) is divisible by \(p\).
  apply Nat.Prime.dvd_choose_self hp
  omega
  omega

theorem number_theory_4805_2 {p : ℕ} (hp : p.Prime) (a : ℕ) : a^p ≡ a [MOD p] := by
  have h : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.eq_iff_modEq_nat p]
  simp [ZMod.pow_card]