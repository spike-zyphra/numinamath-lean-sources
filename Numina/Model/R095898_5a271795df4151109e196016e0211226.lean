import Mathlib

theorem algebra_162355 {w x y z : ℝ} (h₀ : w / x = 4 / 3) (h₁ : y / z = 3 / 2) (h₂ : z / x = 1 / 6) :
    w / y = 16 / 3 := by
  have hx1 : x ≠ 0 := by 
    by_contra h
    rw [h] at h₀ 
    norm_num at h₀
  have h3 : z = x / 6 := by 
    field_simp [hx1] at h₂ 
    linarith 
  have hz1 : z ≠ 0 := by
    by_contra h
    have hx1' : x = 0 := by linarith [h3, h] 
    contradiction 
  -- Substitute into h₁: y / z = 3/2, we have y / (x/6) = 3/2, so y = (3/2) * (x/6)
  have h4 : y = x / 4 := by 
    rw [h3] at h₁ 
    field_simp [hx1] at h₁
    linarith 
  -- From h₀: w / x = 4/3, we obtain w = (4/3) * x
  have h5 : w = 4 / 3 * x := by 
    field_simp [hx1] at h₀ 
    linarith
  -- Then w / y = ( (4/3) * x ) / ( x/4 ) = (4/3) * 4 = 16/3
  have hy1 : y ≠ 0 := by 
    by_contra h 
    rw [h] at h4 
    have hx1' : x = 0 := by linarith 
    exfalso 
    exact hx1 hx1' 
  -- hence w/y is well defined.
  have h6 : w / y = 16 / 3 := by 
    rw [h5, h4]
    -- Using h2', we derive the theorem
    have hx1' : x ≠ 0 := hx1 
    field_simp [hx1']
    <;> nlinarith 
    all_goals try { tauto } 
  exact h6 
  all_goals try { linarith } 
  all_goals try { tauto }
  all_goals try { nlinarith }
  all_goals try { linarith }