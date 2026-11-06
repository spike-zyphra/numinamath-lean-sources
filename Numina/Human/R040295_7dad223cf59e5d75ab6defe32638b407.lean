import Mathlib

open Real Set
open scoped BigOperators

/- 78 Given $x \geqslant 0, y \geqslant 0$, and $x+y \leqslant 2 \pi$, try to find the maximum and minimum values of the function $f(x, y)=\sin x+\sin y- \sin (x+y)$. -/
theorem algebra_251725 :
    IsGreatest {sin x + sin y - sin (x + y) | (x : ℝ) (y : ℝ) (_ : 0 ≤ x) (_ :  0 ≤ y) (_ : x + y ≤ 2 * π)} (3 * √ 3 / 2) ∧
    IsLeast {sin x + sin y - sin (x + y) | (x : ℝ) (y : ℝ) (_ : 0 ≤ x) (_ :  0 ≤ y) (_ : x + y ≤ 2 * π)} (0) := by
  -- first we prove a lemma to convert the expression to sin((x+y)/2) * (cos ((x-y)/2) - cos ((x+y)/2)), both parts use this
  have aux (x y : ℝ) : sin x + sin y - sin (x + y) = 2 * sin ((x + y) / 2) * (cos ((x - y) / 2) - cos ((x + y) / 2)) := by
    have sin_add_sin (a b : ℝ) : sin a + sin b = 2 * sin ((a + b)/2) * cos ((a - b)/2) := by
      rw [two_mul_sin_mul_cos]
      ring_nf
    have sin_two_mul' (a : ℝ) : sin a = 2 * sin (a/2) * cos (a/2) := by
      rw [← sin_two_mul]
      ring_nf
    rw [sin_add_sin]
    nth_rw 2 [sin_two_mul']
    rw [← mul_sub, ← neg_sub, cos_sub_cos]
  simp_rw [aux]
  constructor
  -- first we prove greatest part
  . constructor
    -- 2 * π / 3 and 2 * π / 3 are witness that prove 3 √3/2 belongs to set, we write them like following to use mathlib theorems for evaluating
    . use π/6 + π/2, π/6 + π/2
      simp
      and_intros
      . ring_nf
        gcongr
        norm_num
      . positivity
      . simp [sin_add_pi_div_two, cos_add_pi_div_two]
        ring
    -- to prove upper bound, we introduce t = (x + y)/4
    . rintro z h
      obtain ⟨x, y, hx, hy, hxy, h⟩ := h
      set t := (x + y) / 4
      have hxyt : (x + y) / 2 = 2 * t := by ring
      have ht_lb : 0 ≤ t := by positivity
      have ht_ub : t ≤ π / 2 := by linarith
      rw [← h, hxyt]
      -- now we form a chain of inequalities
      calc
        2 * sin (2 * t) * (cos ((x - y) / 2) - cos (2 * t)) ≤ 2 * sin (2 * t) * (1 - cos (2 * t)) := by
          gcongr
          . simp
            apply Real.sin_nonneg_of_nonneg_of_le_pi
            . positivity
            . linarith
          . exact cos_le_one ((x - y) / 2)
        -- convrt to only sin t and cos t
        _ = 8 * sin t ^ 3 * cos t := by
          rw [sin_two_mul, cos_two_mul', cos_sq']
          ring
        -- we'll use square root to force cos^2 t, then we can get all sin^2 t
        _ = 8 * √((sin t ^ 3) ^ 2 * cos t ^ 2) := by
          rw [sqrt_mul (by positivity)]
          rw [sqrt_sq, sqrt_sq]
          . ring
          . apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
            . linarith
            . assumption
          . apply pow_nonneg
            apply Real.sin_nonneg_of_nonneg_of_le_pi
            . assumption
            . linarith
        -- now we get a format of product of terms, we can then use am-gm
        _ = 8 * (√(1/3) * √(sin t ^ 2 * sin t ^ 2 * sin t ^ 2 * (3 - 3 * sin t ^ 2))) := by
          rw [← sqrt_mul (by norm_num)]
          congr 2
          rw [cos_sq']
          ring
        -- we use am-gm to get a numerical value
        _ ≤ 8 * (√(1/3) * √((3/4) ^ 4)) := by
          gcongr
          clear * - ht_ub ht_lb
          have hw : 0 ≤ (1:ℝ)/4 := by norm_num
          have h₁ : 0 ≤ sin t ^ 2 := by positivity
          have h₂ : 0 ≤ 3 - 3 * sin t ^ 2 := by
            suffices sin t ^ 2 ≤ 1 by linarith
            exact sin_sq_le_one t
          have h := geom_mean_le_arith_mean4_weighted hw hw hw hw h₁ h₁ h₁ h₂ (by norm_num)
          rw [← mul_rpow (by positivity) (by assumption)] at h
          rw [← mul_rpow (by positivity) (by assumption)] at h
          rw [← mul_rpow (by positivity) (by assumption)] at h
          replace h := Real.rpow_le_rpow (by positivity) h (show 0 ≤ (4 : ℝ) by norm_num)
          convert h using 1
          . rw [← rpow_mul (by positivity)]
            simp
          . ring_nf
        _ = 3 * √3 / 2 := by
          ring_nf
          have : √3 ≠ 0 := by simp
          field_simp
          ring_nf
          rw [show (81 : ℝ) = 9^2 by norm_num, show (256 : ℝ) = 16^2 by norm_num]
          simp
          norm_num
  -- the least part
  . constructor
    -- 0, 0 are witness to prove 0 belongs to set
    . use 0, 0
      simp
      exact pi_nonneg
    -- to prove 0 is lower bound is easy, we get expression to be product of 3 sines, all of which are nonnegative
    . rintro z h
      obtain ⟨x, y, hx, hy, hxy, h⟩ := h
      rw [← neg_sub, cos_sub_cos] at h
      ring_nf at h
      rw [← h]
      have : 0 ≤ sin (x * (1 / 2) + y * (1 / 2)) := by
        apply Real.sin_nonneg_of_nonneg_of_le_pi <;> linarith
      have : 0 ≤ sin (x * (1 / 2)) := by
        apply Real.sin_nonneg_of_nonneg_of_le_pi <;> linarith
      have : 0 ≤ sin (y * (1 / 2)) := by
        apply Real.sin_nonneg_of_nonneg_of_le_pi <;> linarith
      positivity