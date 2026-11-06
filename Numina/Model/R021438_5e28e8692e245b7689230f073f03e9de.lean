import Mathlib

theorem inequalities_298700 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 1) :
    Real.sqrt (4 * a + 1) + Real.sqrt (4 * b + 1) + Real.sqrt (4 * c + 1) +
    Real.sqrt (4 * d + 1) < 6 := by

  have h1 : ∀ (x : ℝ) (hx : 0 < x) (hx1 : x < 1), Real.sqrt (4 * x + 1) < 1 + 2 * x := by
    intro x hx hx1
    have h2 : Real.sqrt (4 * x + 1) ≥ 0 := by positivity
    have h3 : (1 + 2 * x) ^ 2 > 4 * x + 1 := by
      nlinarith [show x > 0 by linarith, show x < 1 by linarith]
    have h4 : (1 + 2 * x) > 0 := by linarith
    have h5 : Real.sqrt ( (1 + 2 * x) ^ 2 ) = (1 + 2 * x) := by
      rw [Real.sqrt_sq]
      all_goals linarith
    have h6 : Real.sqrt (4 * x + 1) < Real.sqrt ( (1 + 2 * x) ^ 2 ) := by
      apply Real.sqrt_lt_sqrt
      all_goals nlinarith
    rw [h5] at h6
    linarith
  
  have h1a : Real.sqrt (4 * a + 1) < 1 + 2 * a := by 
    apply h1 a (by linarith) (by
      nlinarith
    )

  have h1b : Real.sqrt (4 * b + 1) < 1 + 2 * b := by 
    apply h1 b (by linarith) (by
      nlinarith
    )

  have h1c : Real.sqrt (4 * c + 1) < 1 + 2 * c := by 
    apply h1 c (by linarith) (by
      nlinarith
    )

  have h1d : Real.sqrt (4 * d + 1) < 1 + 2 * d := by 
    apply h1 d (by linarith) (by 
      nlinarith 
    )

  have h2 : Real.sqrt (4 * a + 1) + Real.sqrt (4 * b + 1) + Real.sqrt (4 * c + 1) +
      Real.sqrt (4 * d + 1) < (1 + 2 * a) + (1 + 2 * b) + (1 + 2 * c) + (1 + 2 * d) := by
    linarith [h1a, h1b, h1c, h1d]

  have h3 : (1 + 2 * a) + (1 + 2 * b) + (1 + 2 * c) + (1 + 2 * d) = 6 := by
    nlinarith

  linarith [h2, h3]