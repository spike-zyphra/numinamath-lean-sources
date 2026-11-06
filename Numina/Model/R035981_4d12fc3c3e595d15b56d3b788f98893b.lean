import Mathlib

theorem algebra_290088 {f : ℝ → ℝ} (hf : ∃ a b, f = fun x => a * x + b)
    (hk : f k = 4) (hfk : f (f k) = 7) (hfn : f (f (f k)) = 19) :
    k = 13 / 4 := by
  rcases hf with ⟨a, b, hfab⟩
  have eq1 : f k = a * k + b := by simp [hfab]
  have eq2 : f (f k) = a * (f k) + b := by simp [hfab]
  have eq3 : f (f (f k)) = a * (f (f k)) + b := by simp [hfab]
  rw [eq1] at hk
  rw [eq2] at hfk
  rw [eq3] at hfn
  -- Now, we substitute hk into hfk
  have eq4 : a * 4 + b = 7 := by
    rw [show f k = (4 : ℝ) by linarith [hk]] at hfk
    linarith
  -- Similarly, substitute hfk into hfn
  have eq5 : a * 7 + b = 19 := by
    rw [show f (f k) = (7 : ℝ) by linarith [hfk]] at hfn
    linarith
  -- Now to solve the system
  have eq6 : a = 4 := by 
    linarith [eq4, eq5]
  have eq7 : b = -9 := by 
    rw [eq6] at eq4
    linarith 
  -- Now to solve the original equation
  have eq8 : a * k + b = 4 := by
    linarith [hk]
  rw [eq6, eq7] at eq8
  -- Now solve for k
  have eq9 : k = 13 / 4 := by
    linarith
  linarith [eq9]