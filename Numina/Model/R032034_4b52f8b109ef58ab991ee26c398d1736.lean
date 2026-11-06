import Mathlib



theorem inequalities_277302 (p n : ℝ) (a b : ℝ) (ha : 0 < b) (hb : b < a)
    (hp : p > n) :
    (a ^ p - b ^ p) / (a ^ p + b ^ p) > (a ^ n - b ^ n) / (a ^ n + b ^ n) := by
  have ha' : a > 0 := by linarith
  have h2 : a ^ p + b ^ p > 0 := by
    apply add_pos
    ·
      apply Real.rpow_pos_of_pos
      linarith
    ·
      apply Real.rpow_pos_of_pos
      linarith
  have h3 : a ^ n + b ^ n > 0 := by
    apply add_pos
    ·
      apply Real.rpow_pos_of_pos
      linarith
    ·
      apply Real.rpow_pos_of_pos
      linarith
  have h6 : a ^ (p - n) > b ^ (p - n) := by
    have h7 : b > 0 := by linarith
    have h8 : 0 < a := by linarith
    have h9 : b < a := by linarith
    have h10 : 0 < p - n := by linarith
    have h11 : b ^ (p - n) < a ^ (p - n) := by
      apply Real.rpow_lt_rpow
      all_goals
      linarith
    linarith
  have h23 : a ^ p * b ^ n - a ^ n * b ^ p > 0 := by
    have h7 : a ^ n * b ^ n > 0 := by positivity
    have h8 : a ^ p * b ^ n - a ^ n * b ^ p > 0 := by
      have h9 : a ^ p = a ^ n * a ^ (p - n) := by 
        rw [← Real.rpow_add]
        ring_nf 
        all_goals
        linarith
      have h10 : b ^ p = b ^ n * b ^ (p - n) := by 
        rw [← Real.rpow_add]
        ring_nf 
        all_goals 
        linarith
      rw [h9, h10]
      nlinarith [show 0 < a ^ n * b ^ n by positivity, h6]
    linarith
  have h1 : (a ^ p - b ^ p) * (a ^ n + b ^ n) - (a ^ n - b ^ n) * (a ^ p + b ^ p) > 0 := by
    nlinarith [h23] 
  apply (div_lt_div_iff (by positivity) (by positivity)).mpr
  nlinarith