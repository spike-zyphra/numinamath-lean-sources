import Mathlib

theorem algebra_7781 {n m : ℕ} (hn : n > 0) (hm : m > 0)
    (hnm : m = 2 * n) (havg : (n * 4 + m * 10) / (n + m) = x) :
    x = 8 := by 

  have h1 : m = 2 * n := hnm
  have eq1 : n * 4 + m * 10 = 24 * n := by
    rw [show m = 2 * n by linarith]
    all_goals omega
  have eq2 : n + m = 3 * n := by 
    rw [show m = 2 * n by linarith]
    all_goals omega
  have eq3 : (n * 4 + m * 10) / (n + m) = 8 := by 
    rw [eq1, eq2]
    have h9 : (24 * n) / (3 * n) = 8 := by 
      have h8 : 24 * n = (3 * n) * 8 := by 
        ring
      rw [h8] 
      have h0 : ((3 * n) * 8) / (3 * n) = 8 := by 
        have h4 : 3 * n > 0 := by 
          omega 
        have h12 : ((3 * n) * 8) / (3 * n) = 8 := by
          field_simp 
          all_goals omega 
        exact_mod_cast h12 
      exact_mod_cast h0 
    exact h9 
  have eq4 : x = 8 := by 
    linarith [havg, eq3]
  exact eq4