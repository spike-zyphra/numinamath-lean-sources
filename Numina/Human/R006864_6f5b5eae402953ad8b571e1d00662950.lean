import Mathlib

open Finset

-- prove a lemma that use in the solution, saying that if p ∣ a - 1, then p ^ k ∣ a ^ p ^ (k - 1) - 1, using induction to prove this. 
lemma prime_dvd_pow (p k a: ℕ) (dvd1 : (p : ℤ) ∣ a - 1) :
  (p ^ k : ℤ) ∣ a ^ (p ^ (k - 1)) - (1 : ℤ) := by 
  induction k with
  | zero => 
    simp
  | succ n ih => 
    by_cases hn0 : n = 0
    -- the case n = 0
    · simp [hn0]
      exact dvd1
    -- the case n ≥ 1
    have nge1 : n ≥ 1 := by 
      omega
    apply Int.ModEq.dvd 
    obtain ⟨m, hm⟩ := ih 
    have hm1 : ↑a ^ p ^ (n - 1) = p ^ n * m + 1 := by 
      linarith
    have eq1 : (a : ℤ) ^ p ^ (n + 1 - 1) = (a ^ p ^ (n - 1)) ^ p := by 
      rw [←pow_mul]
      congr
      have eq2 : n + 1 - 1 = n - 1 + 1 := by 
        omega
      rw [eq2, pow_add]
      simp
    rw [eq1, hm1, add_pow]
    have seteq : range (p + 1) = insert (0 : ℕ) (Icc 1 p) := by 
      refine Finset.ext_iff.mpr ?_
      simp
      omega
    simp [seteq, sum_insert]
    have modeq1 : ∑ x ∈ Icc 1 p, (↑p ^ n * m) ^ x * ↑(p.choose x) ≡ 0 [ZMOD p ^ (n + 1)] := by 
      apply Int.modEq_of_dvd 
      simp
      apply dvd_sum
      intro i hi
      simp at hi
      obtain ⟨h1, h2⟩ := hi
      rw [mul_pow, ←pow_mul]
      by_cases hi2 : i ≥ 2 
      -- the case i ≥ 2 
      have ineq : n * i ≥ n + 1 := by 
        nlinarith
      have dvd2 : (p : ℤ) ^ (n + 1) ∣ ↑p ^ (n * i) := by 
        exact pow_dvd_pow (p : ℤ) ineq
      rw [mul_assoc]
      exact Dvd.dvd.mul_right dvd2 (m ^ i * ↑(p.choose i))
      have ieq1 : i = 1 := by omega
      rw [ieq1]
      simp
      have eq2 : ↑p ^ n * m * (p : ℤ) = p ^ (n + 1) * m := by 
        ring
      rw [eq2]
      simp
    calc 
      _ ≡ 1 + 0 [ZMOD p ^ (n + 1)] := by 
        simp
      _ ≡ 1 +  ∑ x ∈ Icc 1 p, (↑p ^ n * m) ^ x * ↑(p.choose x) [ZMOD p ^ (n + 1)] := by 
        exact Int.ModEq.add rfl (id (Int.ModEq.symm modeq1))
    

theorem number_theory_641894 (p a : ℕ) (hp : Odd p ∧ Nat.Prime p)
  (hpa : ¬p ∣ a) (d : ℕ) (hd : d = orderOf (a : ZMod p)) (h : ¬a ^ d ≡ 1 [MOD p ^ 2])
  (k : ℕ) (hk : 0 < k) : p ^ k ∣ a ^ (d * p ^ (k - 1)) - 1 := by 
  zify
  rw [Nat.cast_sub]
  norm_num
  rw [pow_mul]
  have pdvd : (p : ℤ) ∣ a ^ d - (1 : ℤ) := by 
    have aux : (a : ZMod p) ^ d = 1 := by 
      rw [hd]
      exact pow_orderOf_eq_one (a : ZMod p)
    refine (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (↑a ^ d) p).mp ?_
    norm_num
    exact id (Eq.symm aux)
  have pdvd' : ↑p ∣ (a ^ d : ℕ) - (1 : ℤ) := by 
    norm_num
    exact pdvd
  obtain h1 := prime_dvd_pow p k (a ^ d) pdvd' 
  norm_num at h1
  exact h1
  have aneq : a ≠ 0 := by 
    by_contra hc
    rw [hc] at hpa
    simp at hpa
  have apos : a > 0 := by 
    omega
  exact Nat.one_le_pow (d * p ^ (k - 1)) a apos
  