import Mathlib

/- Solve the following system of equations:

$$
\frac{x y}{x+y}=\frac{1}{3}, \quad \frac{y z}{y+z}=\frac{1}{4}, \quad \frac{z x}{z+x}=\frac{1}{5} .
$$ -/
theorem algebra_255658 {x y z : ℝ} (hd1 : x+y≠0) (hd2 : y+z≠0) (hd3 : z+x≠0) (h1 : x * y / (x + y) = 1 / 3) (h2 : y * z / (y + z) = 1 / 4) (h3 : z * x / (z + x) = 1 / 5) : x = 1 / 2 ∧ y = 1 ∧ z = 1 / 3 := by
  
  -- Some basic facts needed later.
  have xneq0 : x ≠ 0 := by 
    by_contra xeq0
    rw [xeq0] at h1
    norm_num at h1
  have yneq0 : y ≠ 0 := by
    by_contra yeq0
    rw [yeq0] at h2
    norm_num at h2
  have zneq0 : z ≠ 0 := by
    by_contra zeq0
    rw [zeq0] at h3
    norm_num at h3
  
  -- We let u v w be 1/x, 1/y, 1/z respectively and then set up the equations for them based on the assumptions.
  let u:ℝ := 1/x
  let v:ℝ := 1/y
  let w:ℝ := 1/z

  have eq1 : v + u = 3 := by
    have : (x+y) / (x*y) = 3 := by 
      field_simp at h1 ⊢; ring_nf at h1 ⊢; symm; assumption 
    have : (x+y) / (x*y) = 1/y + 1/x := by field_simp; left; ring_nf
    have : 1/y + 1/x = v + u := by simp [v,u]
    linarith
  have eq2 : w + v = 4 := by 
    have : (y+z) / (y*z) = 4 := by 
      field_simp at h2 ⊢; ring_nf at h2 ⊢; symm; assumption 
    have : (y+z) / (y*z) = 1/z + 1/y := by field_simp; left; ring_nf
    have : 1/z + 1/y = w + v := by simp [w,v]
    linarith
  have eq3 : u + w = 5 := by 
    have : (z+x) / (z*x) = 5 := by 
      field_simp at h3 ⊢; ring_nf at h3 ⊢; symm; assumption 
    have : (z+x) / (z*x) = 1/x + 1/z := by field_simp; left; ring_nf
    have : 1/x + 1/z = u + w := by simp [u,w]
    linarith

  --Now simply solve the equations for u,v,w and then we get the value for x y z. The rest is trivial calculations.
  have ueq: u = 2 := by linarith
  have veq: v = 1 := by linarith
  have weq: w = 3 := by linarith
  have : x = 1/2 := by simp [u] at ueq; field_simp at ueq ⊢; linarith
  have : y = 1 := by simp [v] at veq; linarith
  have : z = 1/3 := by simp [w] at weq; field_simp at weq ⊢; linarith

  tauto