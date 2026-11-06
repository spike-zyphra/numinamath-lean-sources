import Mathlib

theorem algebra_194641 {x y z : ℝ} (h : x ≠ y ∧ y ≠ z ∧ z ≠ x)
    (h1 : (1 - 1 / 3) * x = (1 + 1 / 3) * y) (h2 : (1 - 1 / 4) * y = (1 + 1 / 4) * z)
    (h3 : (1 - 1 / 10) * z = (1 + 1 / 10) * x) (h4 : x = 9) (h5 : y = 9) (h6 : z = 9) :
    x = 12 ∧ y = 8 ∧ z = 7 := by
  rw [show x = (9 : ℝ) by linarith [h4], show y = (9 : ℝ) by linarith [h5]] at h1
  norm_num at h1
  all_goals try { 
    exfalso 
    <;> try { 
      tauto 
    } 
    <;> try { 
      linarith 
    } 
    <;> try { 
      tauto 
    }
    <;> try { 
      tauto 
    }
  }