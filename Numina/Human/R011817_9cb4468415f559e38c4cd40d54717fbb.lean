import Mathlib

theorem algebra_314811 (x y : ℤ) (h : 15 * x^2 * y^2 = 35 * x^2 - 3 * y^2 + 412) :
    15 * x^2 * y^2 = 960 := by 
  have eq1 : (5 * x ^ 2 + 1) * (3 * y ^ 2 - 7) = 405 := by 
    linarith
  have eq2 : (405 : ℤ) = 3 ^ 4 * 5 := by norm_num
  rw [eq2] at eq1
  have dvd1 : 3 ^ 4 ∣ (5 * x ^ 2 + 1) * (3 * y ^ 2 - 7) := by
    rw [eq1]
    simp
    norm_num
  have ndvd1 : ¬ 3 ∣ 3 * y ^ 2 - 7 := by 
    by_contra h1
    have aux : 3 ∣ 3 * y ^ 2 := by 
      simp
    have aux2 : 3 ∣ 3 * y ^ 2 - (3 * y ^ 2 - 7) := dvd_sub aux h1
    ring_nf at aux2
    norm_num at aux2
  have ndvd2 : ¬ 3 ^ 4 ∣ 3 * y ^ 2 - 7 := by 
    by_contra hc
    have aux : 3 ∣ 3 * y ^ 2 - 7  := by omega
    exact ndvd1 aux
  have dvdr1 : 3 ^ 4 ∣ 5 * x ^ 2 + 1 := by 
    refine Prime.pow_dvd_of_dvd_mul_right ?_ 4 ndvd1 dvd1
    norm_num
  obtain ⟨k, hk⟩ := dvdr1
  have kpos : k > 0 := by 
    by_contra hc
    simp at hc
    nlinarith
  have ndvd2 : ¬ 5 ∣ 5 * x ^ 2 + 1 := by 
    omega
  have dvd2 : 5 ∣ (5 * x ^ 2 + 1) * (3 * y ^ 2 - 7) := by omega
  have dvr2 : 5 ∣ 3 * y ^ 2 - 7 := by
    refine Int.dvd_of_dvd_mul_right_of_gcd_one dvd2 ?_
    refine Int.isCoprime_iff_gcd_eq_one.mp ?_
    refine IsCoprime.mul_add_left_right ?_ (x ^ 2)
    norm_num
  obtain ⟨t, ht⟩ := dvr2
  have tpos : t > 0 := by 
    by_contra hc
    simp at hc
    rw [ht, hk] at eq1
    nlinarith
  rw [ht, hk] at eq1
  have kteq : k * t = 1 := by nlinarith
  have kteq1 : k = 1 ∧ t = 1 := by
    have kle : k ≤ 1 := by 
      nlinarith
    have kge : k ≥ 1 := by 
      exact kpos
    constructor
    linarith
    have tle : t ≤ 1 := by 
      nlinarith
    have tge : t ≥ 1 := by 
      exact tpos
    linarith
  obtain ⟨keq, teq⟩ := kteq1
  rw [keq] at hk
  rw [teq] at ht
  have xeq : 5 * x ^ 2 = 80 := by nlinarith
  have yeq : 3 * y ^ 2 = 12 := by nlinarith
  nlinarith