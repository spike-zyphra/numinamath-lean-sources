import Mathlib

open Real

theorem algebra_128645 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h1 : 1 / a + 1 / b ≤ 2 * sqrt 2) (h2 : (a - b) ^ 2 = 4 * (a * b) ^ 3) :
    logb a b = -1 := by
  have h11 : a + b ≤ 2 * sqrt 2 * (a * b) := by
    have pos1 : 0 < a * b := mul_pos ha hb
    have h1' : 1 / a + 1 / b = (a + b) / (a * b) := by
      field_simp
      <;> ring
    rw [h1'] at h1
    have h12 : (a + b) / (a * b) ≤ 2 * sqrt 2 := by linarith
    have : (a + b) = (a + b) / (a * b) * (a * b) := by
      field_simp [pos1]
      <;> ring
    rw [this]
    nlinarith [h12, mul_pos (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2) (show (0 : ℝ) < a * b by positivity), Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
  
  have h12 : (a + b) ^ 2 ≤ 8 * (a * b) ^ 2 := by
    have h11' : a + b ≤ 2 * sqrt 2 * (a * b) := by linarith
    have h14 : (a + b) ^ 2 ≤ (2 * sqrt 2 * (a * b)) ^ 2 := by nlinarith [sq_nonneg (a + b - 2 * sqrt 2 * (a * b)), Real.sqrt_nonneg 2, Real.sqrt_nonneg (2 ^ 2), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), sq_nonneg (sqrt 2 * (a * b)), sq_nonneg (a * b)]
    have h13 : (2 * sqrt 2 * (a * b)) ^ 2 = 8 * (a * b) ^ 2 := by
      calc
        (2 * sqrt 2 * (a * b)) ^ 2 = 4 * (sqrt 2) ^ 2 * (a * b) ^ 2 := by ring
        _ = 4 * 2 * (a * b) ^ 2 := by rw [Real.sq_sqrt (by norm_num)]
        _ = 8 * (a * b) ^ 2 := by ring
    nlinarith

  have h2' : (a * b) ^ 3 = ( (a - b) ^ 2 ) / 4 := by
    linarith

  have h31 : logb a b = log b / log a := by 
    field_simp [logb]

  have equal1 : (a * b) * ( (a * b) -1) ^ 2 =0 :=by 
    nlinarith [h11, h12, mul_pos ha hb, sq_nonneg (a - b), sq_nonneg (a * b -1), sq_nonneg (a + b), sq_nonneg (a * b), sq_nonneg (a * b - 1 / 2), sq_nonneg (a * b * b * a), Real.sqrt_nonneg 2, Real.sqrt_nonneg 5, Real.sqrt_nonneg (2 ^ 2 + 5 ^ 2), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 ^ 2 : ℝ) by norm_num)]

  cases' (mul_eq_zero.mp equal1) with eq2 eq3
  · -- Case `a * b = 0`.
    nlinarith [show 0 ≤ a * b by positivity]

  · -- Case `(a * b -1) ^ 2 =0`
    have hab : a * b =1 := by 
      nlinarith [pow_eq_zero eq3]

    have pass : a * b =1 := by 
      linarith

    have a1 : a =1 / b := by 
      field_simp [(show b ≠0 by linarith)]
      <;> nlinarith

    have h32 : log a = - log b := by 
      rw [a1]
      have h881 : log ((1 / b) : ℝ) = - log b := by 
        simp [log_div, log_one]
      linarith [h881]

    rw [h31]
    have pos1 : log b ≠ 0 := by 
      by_contra h
      have h99 : b =1 := by 
        rw [log_eq_zero] at h
        rcases h with (r | r | r)
        · -- b =1
          linarith
        · --b=1
          linarith
        · --b=1
          linarith
      rw [show b =1 by linarith] at pass
      nlinarith [sq_nonneg (a * 1), h11, sq_nonneg (a - 1), sq_nonneg (b - 1)]

    rw [h32]
    field_simp [pos1]
    <;> nlinarith