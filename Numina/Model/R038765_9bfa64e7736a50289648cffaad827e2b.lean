import Mathlib

theorem algebra_324759 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x * y = x / y ∧ x / y = x - y) :
    x + y = -3 / 2 := by
  rcases hxy with ⟨h1, h2⟩
  have eq1 : x * y ^ 2 = x := by
    have h1' : x * y = x / y := by linarith
    field_simp [hy] at h1' 
    nlinarith
  
  have eq2 : x * (y ^ 2 - 1) = 0 := by
    linarith [eq1]

  have eq3 : y ^ 2 - 1 = 0 := by
    apply (mul_left_inj' hx).mp
    linarith
  
  have eq4 : y ^ 2 = 1 := by linarith
  
  have h3 : y = 1 ∨ y = -1 := by 
    rw [sq_eq_one_iff] at eq4
    exact_mod_cast eq4

  rcases h3 with (h3 | h3)
  · -- Suppose $y = 1$
    have eq5 : x / y = x - y := by linarith [h2]
    rw [show y = 1 by linarith] at eq5 
    norm_num at eq5
    all_goals linarith
  · -- Suppose $y = -1$
    have eq5 : x / y = x - y := by linarith [h2]
    rw [show y = -1 by linarith] at eq5 
    norm_num at eq5 
    have eq6 : x = -1 / 2 := by
      nlinarith 
    rw [eq6, h3]
    norm_num