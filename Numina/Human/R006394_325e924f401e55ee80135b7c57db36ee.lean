import Mathlib

theorem number_theory_636605 (a m n : ℤ) (mpos : m > 0) (npos : n > 0)
  (ha : 16 ≤ a) (hcoprime : a.gcd 63 = 1) (hm : a ∣ m) (hn : 63 ∣ n) (hsum : m + n = 10 * a + 1008) : m - n = 10 * a - 1008 := by 
  obtain ⟨k, hk⟩ := hm
  obtain ⟨l, hl⟩ := hn
  rw [hk, hl] at hsum
  have h1 : (k - 10) * a = (16 - l) * 63 := by 
    linarith
  have dvd1 : 63 ∣ (k - 10) * a := by
    rw [h1]
    simp
  have cop : IsCoprime 63 a := by
    exact IsCoprime.symm ((fun {m n} => Int.isCoprime_iff_gcd_eq_one.mpr) hcoprime)
  have dvd2 : 63 ∣ k - 10 := by 
    exact IsCoprime.dvd_of_dvd_mul_right cop dvd1
  obtain ⟨c, hc⟩ := dvd2
  have dvd3 : a ∣ 16 - l := by 
    have advd : a ∣ (16 - l) * 63 := by 
      rw [←h1]
      simp
    exact Int.dvd_of_dvd_mul_left_of_gcd_one advd hcoprime
  obtain ⟨c', hc'⟩ := dvd3
  rw [hc, hc'] at h1
  have ceqc' : c = c' := by 
    have aux : (63 * a) * (c - c') = 0 := by 
      linarith
    obtain h2 | h2 :=  mul_eq_zero.mp aux
    · linarith
    · linarith
  have kge : k ≥ 1 := by 
    nlinarith
  have lge : l ≥ 1 := by 
    nlinarith
  -- analysis at hc, then we get c ≥ -1/7, then c≥ 0
  have cge : c ≥ 0 := by 
    nlinarith
  -- analysis at hc', then we get c * a ≤ 15, then c ≤ 0 using a ≥ 16
  have cle : c ≤ 0 := by 
    nlinarith
  have ceq : c = 0 := by 
    exact Eq.symm (Int.le_antisymm cge cle)
  rw [ceq] at hc
  have keq : k = 10 := by
    linarith
  rw [←ceqc', ceq] at hc'
  have leq : l = 16 := by
    linarith
  rw [keq] at hk
  rw [leq] at hl
  rw [keq, leq] at hsum
  rw [hk, hl]
  linarith