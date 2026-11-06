import Mathlib

open Real

/- 7.011. $\frac{\log _{a} \sqrt{a^{2}-1} \cdot \log _{1 / a}^{2} \sqrt{a^{2}-1}}{\log _{a^{2}}\left(a^{2}-1\right) \cdot \log _{\sqrt[3]{a}} \sqrt[6]{a^{2}-1}}$. -/
theorem algebra_187535 {a : ℝ} (ha : 1 < a ) (ha' : a^2 - 1 ≠ 1) :
    logb a (sqrt (a^2 - 1)) * logb (1 / a) (sqrt (a^2 - 1))^2 /
    (logb (a^2) (a^2 - 1) * logb (a ^ ((1 : ℝ) / 3)) ((a ^ 2  - 1) ^ ((1 : ℝ) / 6))) =
    logb a (sqrt (a^2 - 1)) := by
  -- first prove 0 < a^2 - 1 using 1 < a
  have : 0 < a^2 - 1  := by
    have : 1^2 < a^2 := by rel [ha]
    linarith
  -- for ease of working, write b = a^2 - 1
  set b := a^2 - 1
  -- write square roots as 1/2 power
  rw [sqrt_eq_rpow]
  -- prove a lemma that takes out the power from base of log
  have aux {p q r : ℝ} (hp: p > 0) : logb (p ^ q) r = 1 / q * logb p r := by
    rw [← log_div_log, ← log_div_log, log_rpow (by assumption)]
    ring
  -- write 1/a as power of -1 and write powers as real power
  rw [show 1/a = a^(-1:ℝ) by norm_cast; simp]
  rw [← rpow_natCast a]
  -- now use the lemma and take out powers from log's argument
  rw [aux (by positivity)]
  rw [aux (by positivity)]
  rw [aux (by positivity)]
  rw [logb_rpow_eq_mul_logb_of_pos (by assumption)]
  rw [logb_rpow_eq_mul_logb_of_pos (by assumption)]
  -- finally prove log_a(b) can't be 0 and use ring + field_simp to prove result as an identity
  have : logb a b ≠ 0 := by exact logb_ne_zero_of_pos_of_ne_one ha this ha'
  field_simp
  ring