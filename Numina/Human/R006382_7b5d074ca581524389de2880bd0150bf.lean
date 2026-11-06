import Mathlib

open Nat

theorem number_theory_636481 (p d m : ℕ) (hp : Nat.Prime p) 
  (pne2 : p ≠ 2) (pne3 : p ≠ 3) (hd : d = orderOf (3 : ZMod p)) 
  (hm : 0 < m) (a : ℕ → ℤ)
  (ha0 : a 0 = 0) (hak : ∀ k, a (k + 1) = 3 * a k + 1) :
  (p : ℤ) ∣ a (m * d)  := by 
  -- use induction to prove that a n =(3 ^ n - 1) / 2
  have h1 : ∀ n, a n = (3 ^ n - 1) / 2 := by 
    intro n
    induction n with 
    | zero => 
      simp [ha0]
    | succ k ih => 
      rw [hak, ih]
      have dvd1 : (2 : ℤ) ∣ 3 ^ k - 1 := by   
        have heven : Even ((3 : ℤ) ^ k - 1) := by 
          refine Int.even_sub'.mpr ?_
          constructor
          intro h1
          simp
          intro h1 
          refine Odd.pow ?_
          use 1
          simp
        exact even_iff_two_dvd.mp heven
      obtain ⟨m, hm⟩ := dvd1
      have eq1 : (3 : ℤ) ^ k = 2 * m + 1 := by linarith
      rw [pow_add, eq1]
      simp
      omega
  rw [h1]
  -- by the definition of d is the multiplicative order of 3 modulo p, then 3 ^ p = 1 in ZMod p. 
  have modeq1 : 3 ^ d = (1 : ZMod p) := by 
    rw [hd]
    exact pow_orderOf_eq_one 3
  have modeq2 : 3 ^ (m * d) = (1 : ZMod p) := by
    rw [← mul_comm, pow_mul, modeq1]
    simp
  have pdvd1 : (p : ℤ) ∣ 3 ^ (m * d) - 1 := by 
    refine (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (3 ^ (m * d)) p).mp ?_
    norm_num
    exact Eq.symm modeq2
  -- ↑p ∣ (3 ^ (m * d) - 1) / 2 is equivalent to prove that 2 * ↑p ∣ (3 ^ (m * d) - 1)
  refine Int.dvd_div_of_mul_dvd ?_
  have dvd2 : (2 : ℤ) ∣ 3 ^ (m * d) - 1 := by 
    have heven : Even ((3 : ℤ) ^ (m * d) - 1) := by 
      refine Int.even_sub'.mpr ?_
      constructor
      intro h1
      simp
      intro h1 
      refine Odd.pow ?_
      use 1
      simp
    exact even_iff_two_dvd.mp heven
  have cast1 : (3 : ℤ) ^ (m * d) - 1 = (3 ^ (m * d) - 1 : ℕ) := by 
    rw [Nat.cast_sub]
    norm_cast
    exact one_le_pow' (m * d) 2
  rw [cast1] at pdvd1 dvd2 ⊢
  rw [show (2 : ℤ) = ↑(2 : ℕ) by norm_cast] at dvd2 ⊢ 
  norm_cast at pdvd1 ⊢ 
  norm_cast at dvd2
  refine Coprime.mul_dvd_of_dvd_of_dvd ?_ dvd2 pdvd1
  refine coprime_two_left.mpr ?_
  exact Prime.odd_of_ne_two hp pne2