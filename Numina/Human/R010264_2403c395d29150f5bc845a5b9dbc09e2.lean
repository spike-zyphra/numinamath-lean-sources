import Mathlib


open Nat
  
  /-Find the rightmost non-zero digit of the expansion of (20)(13!). -/
theorem number_theory_609102 : 
  (20 * Nat.factorial 13) / 10 ^ (multiplicity 10 (20 * Nat.factorial 13)) % 10 = 6 := by
  -- 6 We can rewrite this as $(10 \* 2)(13 \* 12 \* 11 \* 10 \* 9 \* 8 \* 7 \* 6 \* 5 \* 4 \* 3 \* 2 \* 1)=$ $\left(10^{3}\right)(2 \* 13 \* 12 \* 11 \* 9 \* 8 \* 7 \* 6 \* 4 \* 3)$; multiplying together the units digits for the terms not equal to 10 reveals that the rightmost non-zero digit is 6 . 
  have eq_aux : 20 * Nat.factorial 13 = (10 ^ 3) * ( 2 * 13 * 12 * 11 * 9 * 8 * 7 * 6 * 4 * 3) := by 
    iterate 13 unfold Nat.factorial
    simp
  have mul_eq : multiplicity 10 (20 * Nat.factorial 13) = 3 := by 
    apply multiplicity_eq_of_dvd_of_not_dvd
    rw [eq_aux]
    simp
    norm_num
    intro h'
    rw [eq_aux] at h'
    obtain ⟨c, dvd_eq⟩  := dvd_iff_exists_eq_mul_left.mp h'
    rw [pow_add] at dvd_eq
    simp at dvd_eq
    have not_dvd : ¬ 10000 ∣ 124540416000 := by norm_num
    obtain dvd' := dvd_iff_exists_eq_mul_left.mpr ⟨c, dvd_eq⟩
    exact not_dvd dvd'
  have eq_aux : (20 * Nat.factorial 13) / 10 ^ 3 = ( 2 * 13 * 12 * 11 * 9 * 8 * 7 * 6 * 4 * 3) := by
    iterate 13 unfold Nat.factorial
    simp
  rw [mul_eq, eq_aux]