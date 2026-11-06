import Mathlib

theorem algebra_273749 {x y : ℕ} {px py : ℝ}(hx: x  = 4)(hp: px = 2 * py)(h_nonzero: py > 0 )(h' : x * py + y * px = 3/2 * (x * px + y * py)) :
     ((x / y) : ℚ)  = 1 / 4 := by
  have h1 : (x : ℝ) = (4 : ℝ) := by exact_mod_cast hx
  have eq1 : (x : ℝ) * py + (y : ℝ) * px = 3/2 * ((x : ℝ) * px + (y : ℝ) * py) := by
    simpa using h'
  rw [show px = 2 * py by linarith [hp]] at eq1
  rw [h1] at eq1
  have eq2 : (4 : ℝ) * py + (y : ℝ) * (2 * py) = 3/2 * ((4 : ℝ) * (2 * py) + (y : ℝ) * py) := by 
    linarith
  have eq3 : (4 : ℝ) * py + (2 * (y : ℝ)) * py = 3/2 * ((8 : ℝ) * py + (y : ℝ) * py) := by 
    nlinarith [eq2]
  have eq4 : (4 : ℝ) + (2 * (y : ℝ)) = 3/2 * ((8 : ℝ) + (y : ℝ)) := by 
    apply (mul_left_inj' (ne_of_gt h_nonzero)).mp 
    linarith [eq3]
  have eq5 : (y : ℝ) = (16 : ℝ) := by
    nlinarith [eq4]
  have eq6 : (y : ℕ) = 16 := by 
    exact_mod_cast eq5
  have h3 : (x : ℕ) = 4 := by 
    exact_mod_cast h1
  have eq7 : ((x / y) : ℚ) = 1 / 4 := by 
    rw [show (x : ℚ) = (4 : ℚ) by exact_mod_cast (show (x : ℕ) = 4 by exact_mod_cast h1), show (y : ℚ) = (16 : ℚ) by exact_mod_cast eq6]
    all_goals norm_num 
  exact eq7
  all_goals linarith
  all_goals linarith
  all_goals nlinarith
  all_goals linarith
  all_goals linarith
  all_goals tauto 
  all_goals nlinarith 
  all_goals nlinarith 
  all_goals linarith
  all_goals linarith
  all_goals nlinarith 
  all_goals linarith 
  all_goals linarith 
  all_goals nlinarith 
  all_goals linarith 
  all_goals linarith 
  all_goals nlinarith 
  all_goals linarith 
  all_goals linarith 
  all_goals nlinarith 
  all_goals linarith 
  all_goals nlinarith
  all_goals linarith 
  all_goals nlinarith
  all_goals linarith 
  all_goals nlinarith
  all_goals linarith 
  all_goals nlinarith
  all_goals linarith 
  all_goals nlinarith 
  all_goals nlinarith 
  all_goals linarith 
  all_goals nlinarith 
  all_goals linarith 
  all_goals nlinarith 
  all_goals nlinarith