import Mathlib

theorem algebra_64320 {a b : ℕ} (ha : IsSquare a) (hb : IsSquare b)
    (h : a * b = a + b + 4844) :
    (Real.sqrt a + 1) * (Real.sqrt b + 1) * (Real.sqrt a - 1) * (Real.sqrt b - 1) -
    (Real.sqrt 68 + 1) * (Real.sqrt 63 + 1) * (Real.sqrt 68 - 1) * (Real.sqrt 63 - 1) = 691 := by

  have h1 : (Real.sqrt a + 1 : ℝ) * (Real.sqrt b + 1) * (Real.sqrt a - 1) * (Real.sqrt b - 1) = ((a : ℝ) - 1) * ((b : ℝ) - 1) := by
    have ha1 : Real.sqrt a ^ 2 = (a : ℝ) := by
      rw [Real.sq_sqrt]
      exact_mod_cast show a ≥ 0 by positivity
    have hb1 : Real.sqrt b ^ 2 = (b : ℝ) := by
      rw [Real.sq_sqrt]
      exact_mod_cast show b ≥ 0 by positivity
    calc
      (Real.sqrt a + 1 : ℝ) * (Real.sqrt b + 1) * (Real.sqrt a - 1) * (Real.sqrt b - 1)
          = ((Real.sqrt a + 1) * (Real.sqrt a - 1)) * ((Real.sqrt b + 1) * (Real.sqrt b - 1)) := by ring
      _ = ((Real.sqrt a) ^ 2 - 1) * ((Real.sqrt b) ^ 2 - 1) := by 
        ring_nf
      _ = ((a : ℝ) - 1) * ((b : ℝ) - 1) := by 
        rw [ha1, hb1]

  have h2 : ((a : ℝ) - 1) * ((b : ℝ) - 1) = (4845 : ℝ) := by
    have hab : (a : ℝ) * (b : ℝ) = (a : ℝ) + (b : ℝ) + 4844 := by
      exact_mod_cast h
    nlinarith

  have h3 : (Real.sqrt 68 + 1) * (Real.sqrt 63 + 1) * (Real.sqrt 68 - 1) * (Real.sqrt 63 - 1) = (4154 : ℝ) := by
    have h4 : Real.sqrt 68 ^ 2 = (68 : ℝ) := by
      rw [Real.sq_sqrt]
      norm_num
    have h5 : Real.sqrt 63 ^ 2 = (63 : ℝ) := by 
      rw [Real.sq_sqrt]
      norm_num
    calc
      (Real.sqrt 68 + 1) * (Real.sqrt 63 + 1) * (Real.sqrt 68 - 1) * (Real.sqrt 63 - 1)
          = ((Real.sqrt 68 + 1) * (Real.sqrt 68 - 1)) * ((Real.sqrt 63 + 1) * (Real.sqrt 63 - 1)) := by ring
      _ = ((Real.sqrt 68 : ℝ) ^ 2 - 1) * ((Real.sqrt 63 : ℝ) ^ 2 - 1) := by 
        ring_nf
      _ = ((68 : ℝ) - 1) * ((63 : ℝ) - 1) := by 
        rw [h4, h5]
      _ = (4154 : ℝ) := by 
        norm_num

  rw [h1, h3, h2]
  all_goals norm_num