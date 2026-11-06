import Mathlib

/- Four positive integers form a monotonically increasing sequence, where the first three terms form an arithmetic sequence, and the last three terms form a geometric sequence. If the difference between the last term and the first term is 30, then the sum of these four positive integers is $\qquad$ .-/
theorem algebra_265138 (a : ℕ → ℤ) (h0 : 0 < a 0) (h1 : a 0 < a 1)
    (h2 : a 1 < a 2) (h3 : a 2 < a 3)
    (h_arith : a 0 + a 2 = 2 * a 1) (h_geo : a 1 * a 3 = a 2 ^ 2)
    (h_sub : a 3 - a 0 = 30) :
    a 0 + a 1 + a 2 + a 3 = 129 := by
  -- denote four positive integers by d and a 0
  clear h2 h3
  set d := a 1 - a 0 with hd
  -- denote the a 1
  have ha1 : a 1 = a 0 + d := by
    rw [hd]
    omega
  -- denote the a 2
  have ha2 : a 2 = a 0 + 2 * d := by
    rw [hd]
    omega
  -- denote the a 3
  have ha3 : a 3 = a 0 + 30 := by omega

  -- substitute the a 1, a 2, a 3 into the h_geo
  rw [ha1, ha2, ha3] at h_geo

  replace h_geo : 3 * a 0 * (10 - d) = 2 * d * (2 * d - 15) := by
    linarith only [h_geo]
  -- show that (10 - d) * (2 * d - 15) ≥ 0
  have hd_pos : 3 *a 0 * (10 - d) * (2 * d - 15) ≥ 0 := by
    rw [h_geo]
    have d_pos : 0 < d := by rw [hd]; linarith only [h1]
    calc
      2 * d * (2 * d - 15) * (2 * d - 15) = 2 * d * (2 * d - 15) ^ 2 := by ring_nf
      _ ≥ 0 := by positivity

  -- show that d ≤ 7 or d ≥ 11 or d = 8, 9, 10
  have hd_case := Int.lt_or_le d 11
  rw [show d < 11 ↔ d < 10 + 1 by norm_num, Int.lt_add_one_iff] at hd_case
  rw [Int.le_iff_eq_or_lt] at hd_case
  rw [show d < 10 ↔ d < 9 + 1 by norm_num, Int.lt_add_one_iff] at hd_case
  rw [Int.le_iff_eq_or_lt] at hd_case
  rw [show d < 9 ↔ d < 8 + 1 by norm_num, Int.lt_add_one_iff] at hd_case
  rw [Int.le_iff_eq_or_lt] at hd_case
  rw [show d < 8 ↔ d < 7 + 1 by norm_num, Int.lt_add_one_iff] at hd_case

-- then prove case by case
  rcases hd_case with (hd_case | hd_case | hd_case | hd_case) | hd_case
  . -- case d = 10
    nlinarith
  . -- case d = 9
    rw [hd_case] at h_geo
    ring_nf at h_geo
    -- have a 0 = 18
    have ha0 : a 0 = 18 := by linarith
    rw [ha1, ha2, ha3, ha0, hd_case]
    norm_num
  . -- case d = 8
    rw [hd_case] at h_geo
    ring_nf at h_geo
    -- show that 6 ∣ 16, then contradiction!
    have h_dvd : 6 ∣ (16 : ℤ) := by rw [<-h_geo]; exact Int.dvd_mul_left (a 0) 6
    norm_num at h_dvd
  . -- case d ≤ 7
    nlinarith
  . -- case d ≥ 11
    nlinarith