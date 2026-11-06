import Mathlib

/- Suppose that the measurement of time during the day is converted to the metric system so that each day has 10 metric hours, and each metric hour has 100 metric minutes. Digital clocks would then be produced that would read 9:99 just before midnight, 0:00 at midnight, 1:25 at the former 3:00 AM, and 7:50 at the former 6:00 PM. After the conversion, a person who wanted to wake up at the equivalent of the former 6:36 AM would set his new digital alarm clock for A:BC, where A, B, and C are digits. Find $100A+10B+C$
-/
theorem algebra_95585 (A B C normal_minute metric_minute : ℕ) (normal_time metric_time : ℕ × ℕ) (hnormal : normal_minute = 60*normal_time.1 + normal_time.2) (hmetric : metric_minute = 100*metric_time.1 + metric_time.2) (hratio : metric_minute/normal_minute = (10*100 : ℚ)/(24*60)) (h_normal_time : normal_time = ⟨6,36⟩) (h_metric_time : metric_time = ⟨A,10*B+C⟩) : 100 * A + 10 * B + C = 275 := by
  --We first convert the normal time to minutes.
  have hnormal' : normal_minute = 60*6+36 := by rw [hnormal, h_normal_time]
  simp only [Nat.reduceMul, Nat.reduceAdd] at hnormal'
  --We compute the ratio of the two times.
  rw [hnormal'] at hratio
  norm_num at hratio
  --We compute the metric time in minutes from hratio.
  rw [div_eq_div_iff (by norm_num : (396 :  ℚ) ≠ 0) (by norm_num : (36 : ℚ) ≠ 0)] at hratio
  rw [← eq_div_iff_mul_eq (by norm_num : (36 : ℚ) ≠ 0)] at hratio
  norm_num at hratio
  --We substitute the metric time in minutes into the metric time.
  rw_mod_cast [h_metric_time, hratio] at hmetric
  simp only [← add_assoc] at hmetric
  rw [hmetric]