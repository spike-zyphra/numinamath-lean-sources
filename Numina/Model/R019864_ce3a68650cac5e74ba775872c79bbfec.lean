import Mathlib

theorem algebra_7462 {P : ℝ → ℝ} (hP : ∃ p : Polynomial ℝ, P = fun x => p.eval x)
    (hP1 : P 1 = 0) (hP2 : P 2 = 1) (m n : ℝ) (hP3 : ∀ x, P (x ^ 2) = x ^ 4 + m * x ^ 2 + n) :
    P 0 = 1 := by
  rcases hP with ⟨p, hP⟩
  have eq1 : p.eval 1 = 0 := by 
    rw [hP] at hP1 
    exact_mod_cast hP1 
  have eq2 : p.eval 2 = 1 := by 
    rw [hP] at hP2 
    exact_mod_cast hP2 
  have eq3 := hP3 0 
  norm_num [hP] at eq3 
  have eq4 := hP3 1 
  norm_num [hP] at eq4 
  have eq5 := hP3 2 
  norm_num [hP] at eq5 
  have eq6 := hP3 (Real.sqrt 2)
  have h1 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have h2 : (Real.sqrt 2 : ℝ) ^ 4 = (4 : ℝ) := by
    calc
      (Real.sqrt 2 : ℝ) ^ 4 = ((Real.sqrt 2 : ℝ) ^ 2) ^ 2 := by ring 
      _ = (2 : ℝ) ^ 2 := by rw [h1]
      _ = 4 := by norm_num
  simp [h1, h2, hP] at eq6 
  have eq7 : m = -2 := by 
    nlinarith 
  have eq8 : n = 1 := by 
    linarith 
  -- Now that we know m and n, we can compute p.eval 0, which is the constant term of p.
  -- From eq3: p.eval 0 = n
  -- From eq8: n = 1
  -- Therefore, p.eval 0 = 1
  have eq9 : p.eval 0 = 1 := by 
    nlinarith [eq3, eq8] 
  rw [hP] 
  exact_mod_cast eq9