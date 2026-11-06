import Mathlib

theorem inequalities_240369 (a b t : ℝ) (ha : 0 < b) (hb : b < a)
    (ht : 0 < t) (h : ∃ q : ℚ, t = q) : a ^ t > b ^ t := by
  rcases h with ⟨q, rfl⟩
  have ha' : 0 < a := by linarith
  have h1 : a > b := by linarith
  have h2 : (a : ℝ) ^ (q : ℝ) > (b : ℝ) ^ (q : ℝ) := by
    apply Real.rpow_lt_rpow
    all_goals
      try { linarith }
      try { positivity }
      try { exact_mod_cast ha }
      try { exact_mod_cast ht }
  exact h2