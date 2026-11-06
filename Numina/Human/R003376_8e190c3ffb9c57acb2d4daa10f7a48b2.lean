import Mathlib

open Real

/- Example 13 If $x, y, z$ are positive real numbers, find the maximum value of the function $\frac{x y z}{(1+5 x)(4 x+3 y)(5 y+6 z)(z+18)}$, and prove your conclusion. -/

-- a lemma for inequality with two terms from target, uses am-gm of 2 variable
lemma lemma_1 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : x / ((1 + 5*x) * (4*x + 3*y)) ≤
    1 / (√(15 * y) + 2) ^ 2 := by
  convert_to 1 / (20 * x + 3 * y / x + 15 * y + 4) ≤ _
  . field_simp
    ring_nf
    simp
  apply one_div_le_one_div_of_le
  . positivity
  . calc
    _ = 4 * √(15 * y) + 15 * y + 4 := by
      ring_nf
      rw [sq_sqrt (by positivity)]
      ring
    _ ≤ _ := by
      gcongr
      convert two_mul_le_add_sq (2 * √(5 * x)) (√(3 * y / x)) using 1
      . ring_nf
        rw [← sqrt_mul (by positivity)]
        congr 2
        field_simp
        ring
      . ring_nf
        repeat rw [sq_sqrt (by positivity)]
        ring

-- a lemma for inequality with two terms from target, uses am-gm of two variable
lemma lemma_2 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : x / ((5 * y + 6 * x) * (x + 18)) ≤
    1 / (√(5 * y) + 6 * √3) ^ 2 := by
  convert_to 1 / (90 * y  / x + 6 * x + 5 * y + 108 ) ≤ _
  . field_simp
    ring_nf
    simp
  apply one_div_le_one_div_of_le
  . positivity
  . calc
    _ =  12 * √(5 * y) * √3 + 5 * y + 108 := by
      ring_nf
      simp
      ring_nf
      simp [hy.le]
    _ ≤ _ := by
      gcongr
      convert two_mul_le_add_sq (3 * √(10 * y / x)) (√(6 * x)) using 1
      . simp
        ring_nf
        rw [sqrt_mul (by positivity), show (10 : ℝ) = 2 * 5 by norm_num]
        simp
        rw [sqrt_mul (by positivity)]
        field_simp
        have : √2 * √6 / 2 = √3 := by
          rw [show (6 : ℝ) = 2 * 3 by norm_num]
          simp
          ring_nf
          simp
          ring
        rw [← this]
        ring
      . ring_nf
        repeat rw [sq_sqrt (by positivity)]
        ring

theorem algebra_173885 :
    IsGreatest {x * y * z / ((1 + 5 * x) * (4 * x + 3 * y) * (5 * y + 6 * z) * (z + 18))
    | (x : ℝ) (y : ℝ) (z : ℝ) (_ : 0 < x) (_ : 0 < y) (_ : 0 < z)} (1 / 5120) := by
  constructor
  -- to prove belongs to set, use 3/5, 12/5, 6 for x, y, z
  . simp
    use 3 / 5, 12 / 5, 6
    norm_num
  -- to prove upper bound
  . rintro a ⟨x, y, z, hx, hy, hz, h⟩
    rw [← h]
    calc
    -- break the expression into terms for lemma
    _ = (x / ((1 + 5 * x) * (4 * x + 3 * y))) * (z / ((5 * y + 6 * z) * (z + 18))) * y := by
      field_simp; ring
    -- apply lemma
    _ ≤ (1 / (√(15 * y) + 2) ^ 2) * (1 / (√(5 * y) + 6 * √3) ^ 2) * y := by
      gcongr ?_ * ?_ * y
      . apply lemma_1 _ _ hx hy
      . apply lemma_2 _ _ hz hy
    -- multiply denominator
    _ = 1 / ((√(15 * y) + 2) * (√(5 * y) + 6 * √3) / √y) ^ 2 := by
      field_simp [hy.ne.symm]
      rw [mul_pow]
    -- simplify
    _ = 1 / (5 * √3 * √y + 12 * √3 / √y + 20 * √5)^2 := by
      congr
      simp [show (15 : ℝ) = 3 * 5 by norm_num]
      field_simp
      ring_nf
      simp
      ring
    -- use am-gm of two varibales
    _ ≤ 1 / (2 * √(5 * √3 * 12 * √3) + 20 * √5)^2 := by
      gcongr
      convert two_mul_le_add_sq √(5 * √3 * √y) √(12 * √3 / √y) using 1
      . simp
        field_simp
        ring
      . repeat rw [sq_sqrt (by positivity)]
    -- now convert the numbers to suitable format for norm_num
    _ = _ := by
      ring_nf
      simp
      ring_nf
      simp
      rw [← sqrt_mul (by norm_num), ← sqrt_mul (by norm_num)]
      rw [show (3 * 60 * 5 : ℝ) = 30^2 by norm_num]
      simp
      norm_num