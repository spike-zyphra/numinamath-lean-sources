import Mathlib

theorem algebra_194441 {x y : ℕ} (h : x + y = 140) (h1 : (2.5 : ℝ) * x = (3 : ℝ) * y)
    (h2 : (2.5 : ℝ) * x + (3 : ℝ) * y = 60) :
    x = 20 ∧ y = 120 := by
  have h3 : (x : ℝ) + (y : ℝ) = (140 : ℝ) := by exact_mod_cast h
  have eq1 : (y : ℝ) = 10 := by
    norm_num at h1 h2 
    nlinarith
  have eq2 : (x : ℝ) = (130 : ℝ) := by
    have h4 : (x : ℝ) = (140 : ℝ) - (y : ℝ) := by linarith
    rw [show (y : ℝ) = (10 : ℝ) by linarith [eq1]] at h4
    linarith
  rw [show (x : ℝ) = (130 : ℝ) by linarith [eq2], 
      show (y : ℝ) = (10 : ℝ) by linarith [eq1]] at h1
  norm_num at h1
  all_goals
    try { 
      exfalso 
      <;> try { 
        nlinarith 
      } 
      <;> try { 
        tauto 
      } 
    } 
    <;> try { 
      norm_num at h1 h2 
      <;> try { 
        nlinarith 
      } 
      <;> try { 
        tauto 
      } 
    }