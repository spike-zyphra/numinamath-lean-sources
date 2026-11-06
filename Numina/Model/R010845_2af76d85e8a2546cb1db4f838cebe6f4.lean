import Mathlib

open Real

lemma p67' {a : ℝ} (hapos : 0 < a) : ∀ (x : ℝ), 0 < x → 2 * √a ≤ x + a / x := by
  intro x hxpos
  apply le_of_mul_le_mul_left _ (show (0 : ℝ) < 1 / 2 by linarith)
  rw [mul_add, (show 1 / 2 * (2 * √a) = √a by linarith)]
  nth_rw 1 [← mul_one a, ← div_self (show x ≠ 0 by linarith),← mul_div_assoc, mul_comm a]
  rw [mul_div_assoc,sqrt_mul,sqrt_eq_rpow, sqrt_eq_rpow]
  apply geom_mean_le_arith_mean2_weighted
  simp_all; repeat linarith
  apply div_nonneg (by linarith) (by linarith)
  ring; linarith

noncomputable def f_4079 x := (x^2 + 2 - √(x^4 + 4)) / x

theorem intermediate_algebra_4079  : (∀ x, 0 < x → f_4079 x ≤ 2 * √2 - 2)
            ∧ ∃ x, 0 < x → f_4079 x = 2 * √2 - 2 := by
  constructor
  · intro x hxpos
    have : f_4079 x = 4 / (x + 2/x + √(x^2 + 4/x^2)) := by
      calc
        f_4079 x = (x^2 + 2 - √(x^4 + 4)) / x * 1 := by dsimp [f_4079]; ring
        _ = (x^2 + 2 - √(x^4 + 4)) / x * ((x^2 + 2 + √(x^4 + 4)) / (x^2 + 2 + √(x^4 + 4))) := by
          rw [← div_self]
          apply ne_of_gt
          repeat
            rw [← zero_add 0]
            apply add_lt_add_of_lt_of_lt
          · simp_all
          · simp_all
          · apply sqrt_pos_of_pos
            rw [← zero_add 0]
            apply add_lt_add_of_lt_of_lt
            repeat simp_all
        _ = ((x^2 + 2 - √(x^4 + 4)) * (x^2 + 2 + √(x^4 + 4))) / (x*(x^2 + 2 + √(x^4 + 4))) := by simp_all [div_mul_div_comm]
        _ = 4 * x^2 / (x*(x^2 + 2 + √(x^4 + 4))) := by
          rw [mul_comm, ← sq_sub_sq (x^2 + 2) √(x^4 + 4),sq_sqrt]
          rw [add_pow_two,← pow_mul, (show 2 * 2 = 4 by norm_num)]
          rw [(show 2 * x ^ 2 *2 = 4 * x^2 by ring), (show 2 ^ 2 = (4 : ℝ) by norm_num)]
          simp_all
          rw [← zero_add 0]
          apply add_le_add
          rw [(show x ^ 4 = (x^2)^2 by ring)]
          exact pow_two_nonneg (x^2)
          simp_all
        _ = 4 * x / (x^2 + 2 + √(x^4 + 4)) := by
          rw [pow_two, ← mul_assoc 4,← mul_comm,mul_div_mul_left]
          linarith
        _ = 4 / (x + 2/x + √(x^4 + 4)/x) := by
          nth_rw 1 [← inv_inv x,← div_eq_mul_inv,div_div,mul_comm x⁻¹]
          rw [← div_eq_mul_inv,add_div,add_div,pow_two,mul_self_div_self]
        _ = 4 / (x + 2/x + √((x^4 + 4)/x^2)) := by
          rw [← sqrt_sq (show 0 ≤ x by linarith), ← sqrt_div,sqrt_sq]
          linarith
          rw [← zero_add 0]
          apply add_le_add
          rw [(show 4 = 2 * 2 by norm_num),pow_mul]
          exact pow_two_nonneg (√(x ^ 2) ^ 2)
          linarith
        _ = 4 / (x + 2/x + √(x^2 + 4/x^2)) := by
          rw [add_div,(show 4 = 2 + 2 by norm_num),pow_add,mul_div_assoc]
          rw [div_self,mul_one]
          simp_all; linarith
    rw [this]
    have h₁ : 2 * √2 ≤ x + 2 / x := by
      apply p67' (by linarith); linarith
    have h₂ : 2 ≤ √(x ^ 2 + 4 / x ^ 2) := by
      rw [(show 2 = √(2^2) by aesop)]
      apply sqrt_le_sqrt
      rw [(show 2^2 = (2 : ℝ) * 2 by ring)]
      nth_rw 2 [← sqrt_sq (show 0 ≤ 2 by linarith)]
      rw [(show 2^2 = (4 : ℝ) by ring)]
      apply p67' (by linarith)
      aesop
    have h' : 2 * √2 + 2 ≤ x + 2 / x + √(x ^ 2 + 4 / x ^ 2) := by linarith
    have h'' : 2 * √2 - 2 = 4 / (2*√2 + 2) := by
      field_simp
      <;> ring_nf <;> norm_num
      <;> ring
    have h_le : 4 / (x + 2 / x + √(x ^ 2 + 4 / x ^ 2)) ≤ 2 * √2 - 2 := by
      rw [h'']
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [h', Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (2 : ℝ) ≥ 0)]
    linarith
  · use Real.sqrt 2
    intro h
    have h_eq : f_4079 (Real.sqrt 2) = 2 * Real.sqrt 2 - 2 := by
      dsimp [f_4079]
      have h1 : (Real.sqrt 2) ^ 4 = 4 := by
        calc
          (Real.sqrt 2) ^ 4 = ((Real.sqrt 2) ^ 2) ^ 2 := by ring
          _ = (2) ^ 2 := by rw [Real.sq_sqrt]; positivity
          _ = 4 := by norm_num
      have h2 : Real.sqrt ((Real.sqrt 2) ^ 4 + 4) = 2 * Real.sqrt 2 := by
        rw [h1]
        have h3 : Real.sqrt (4 + 4) = 2 * Real.sqrt 2 := by
          have h4 : Real.sqrt (4 + 4) = Real.sqrt (2^2 * 2) := by norm_num
          rw [h4]
          rw [Real.sqrt_mul]
          rw [Real.sqrt_sq]
          all_goals positivity
        rw [h3]
        <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (2 : ℝ) ≥ 0)]
      rw [h2]
      field_simp
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (2 : ℝ) ≥ 0)]
    linarith [h_eq]