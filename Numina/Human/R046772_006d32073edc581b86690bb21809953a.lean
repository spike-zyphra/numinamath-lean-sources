import Mathlib

open Real

/- Problem 3. Let $a, b, c$ be real numbers such that $1 < b \leq c^{2} \leq a^{10}$, and


$$

\log _{a} b+2 \log _{b} c+5 \log _{c} a=12

$$


Show that


$$

2 \log _{a} c+5 \log _{c} b+10 \log _{b} a \geq 21

$$
 -/
theorem inequalities_113425 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (h1 : 1 < b) (h2 : b ≤ c^2) (h3 : c^2 ≤ a^10)
    (h4 : logb a b + 2 * logb b c + 5 * logb c a = 12) :
    2 * logb a c + 5 * logb c b + 10 * logb b a ≥ 21 := by
  -- first prove 1 < a, 1 < c
  have : 1 < a := by apply lt_of_pow_lt_pow_left₀ 10 <;> linarith
  have : 1 < c := by apply lt_of_pow_lt_pow_left₀ 2 <;> linarith
  -- define the 3 logs as x, y, z
  set x := logb a b with hx
  set y := 2 * logb b c with hy
  set z := 5 * logb c a with hz
  -- x * y * z = 10, by simply using mul_logb
  have h5 : x * y * z = 10 := by
    rw [hx, hy, hz]
    convert_to 10 * (logb a b * logb b c * logb c a) = 10
    . ring
    rw [mul_logb (by linarith) (by linarith) (by linarith)]
    rw [mul_logb (by linarith) (by linarith) (by linarith)]
    rw [logb_self_eq_one (by linarith)]
    norm_num
  -- y and z are >=1 by using b ≤ c^2 ≤ a^10
  have : 1 ≤ y := by
    calc
      (1:ℝ) = logb b b := by rw [logb_self_eq_one (by linarith)]
      _ ≤ logb b (c^2) := by gcongr; assumption
      _ = 2 * logb b c := by rw [logb_pow]; norm_cast
  have : c ≤ a^5 := by
    apply le_of_pow_le_pow_left₀ (n := 2)
    . norm_num
    . apply pow_nonneg (by linarith)
    . linarith
  have : 1 ≤ z := by
    calc
      (1:ℝ) = logb c c := by rw [logb_self_eq_one (by linarith)]
      _ ≤ logb c (a^5) := by gcongr; assumption
      _ = 5 * logb c a := by rw [logb_pow]; norm_cast
  -- this means 0 < x as otherwise xyz is nonpositive
  have : 0 < x := by
    by_contra h
    have : 0 * 0 ≤ -x * (y * z) := by gcongr <;> nlinarith
    linarith
  -- also x ≤ 10 as y * z ≥ 1
  have : x ≤ 10 := by
    rw [← h5]
    nth_rw 1 [show x = x * 1 by ring, mul_assoc]
    gcongr
    nlinarith
  -- finally make the target xy + yz + zx ≥ 21
  convert_to x * y + y * z + z * x ≥ 21
  . rw [hx, hy, hz]
    nth_rw 3 [← mul_logb (show c ≠ 0 by linarith) (by linarith) (by linarith)]
    nth_rw 2 [← mul_logb (show a ≠ 0 by linarith) (by linarith) (by linarith)]
    nth_rw 1 [← mul_logb (show b ≠ 0 by linarith) (by linarith) (by linarith)]
    ring
  -- which is equivalent to x(12-x) + 10/x ≥ 21
  convert_to x * (12 - x) + 10 / x ≥ 21
  . rw [← h4, ← h5]
    have : x ≠ 0 := by
      by_contra h
      rw [hx] at h
      obtain h | h | h | h | h | h := logb_eq_zero.mp h
      all_goals linarith
    field_simp
    ring
  -- this can be proven from (x-1)^2 * (10-x) ≥ 0 (divide by x)
  suffices (x-1)^2 * (10 - x) ≥ 0 * 0 by
    ring_nf at this ⊢
    have : (10 - x * 21 + x ^ 2 * 12 - x ^ 3) / x ≥ 0 := by
      apply div_nonneg <;> linarith
    convert_to 10 * x⁻¹ - 21 + x * 12 - x^2 ≥ 0 at this
    . field_simp
      ring
    linarith
  -- (x-1)^2 is nonnegative and 10 ≥ x, so we're done.
  gcongr
  . positivity
  . linarith