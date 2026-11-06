import Mathlib

theorem algebra_610113 (a : ℤ)(b : ℤ) (apos:0<a) (bpos:0<b) (hab: a < b) (h : ((2020:ℝ) - (a:ℝ))/((a:ℝ)) * ((2020:ℝ) - (b:ℝ))/((b:ℝ)) = 2) :  (a,b)=(505, 1212) := by
  have h1: (2020-a)*(2020-b) = 2*a*b := by
    field_simp [(show (a:ℝ)≠0 by positivity),(show (b:ℝ)≠0 by positivity)] at h
    ring_nf at h ⊢
    norm_cast at h ⊢
    all_goals nlinarith
  have h2: a*b + 2020*(a+b) = 2020^2 := by
    nlinarith
  have ha1: a ≤ 1212 := by
    nlinarith [sq_nonneg (a-b), sq_nonneg (a-2020), sq_nonneg (b-2020),
          h2, mul_pos (show 0 < (a:ℝ) by exact_mod_cast apos) (show 0 < (b:ℝ) by exact_mod_cast bpos)]
  have ha2: b ≤ 2020 := by
    nlinarith [sq_nonneg (a-b), sq_nonneg (a-2020), sq_nonneg (b-2020),
          h2, mul_pos (show 0 < (a:ℝ) by exact_mod_cast apos) (show 0 < (b:ℝ) by exact_mod_cast bpos)]
  have ha3: a > 0 := apos
  have ha4: b > 0 := bpos
  have h3: a = 505 := by
    interval_cases a <;> omega
  have hb1: b = 1212 := by
    rw [h3] at h2 h1
    nlinarith
  simp [h3, hb1]