import Mathlib

/- 4. Solve the system $\left\{\begin{array}{c}x^{2}+y^{2}+2 x+6 y=-5 \\ x^{2}+z^{2}+2 x-4 z=8 \\ y^{2}+z^{2}+6 y-4 z=-3\end{array}\right.$. -/
theorem algebra_132398 (x y z : ℝ) :
    (x^2 + y^2 + 2 * x + 6 * y = -5 ∧ x^2 + z^2 + 2 * x - 4 * z = 8 ∧ y^2 + z^2 + 6 * y - 4 * z = -3) ↔
    (x = 1 ∧ y = -2 ∧ z = -1) ∨ (x = 1 ∧ y = -2 ∧ z = 5) ∨ (x = 1 ∧ y = -4 ∧ z = -1) ∨ (x = 1 ∧ y = -4 ∧ z = 5) ∨
    (x = -3 ∧ y = -2 ∧ z = -1) ∨ (x = -3 ∧ y = -2 ∧ z = 5) ∨ (x = -3 ∧ y = -4 ∧ z = -1) ∨ (x = -3 ∧ y = -4 ∧ z = 5) := by
  
    constructor

    -- from left to right. We will actually prove the range of x,y,z separately.
    -- We combine all three equations and get an equation for x,y,z respectively. Then we can solve them.
    intro h
    obtain ⟨h1,h2,h3⟩ := h
    
    have xr : x = 1 ∨ x = -3 := by 
      have eq: x^2 + 2*x - 3 =0 := by linarith
      have : x^2 + 2*x - 3 = (x+3) * (x-1) := by ring
      rw [this] at eq; simp at eq
      obtain eq1|eq2 := eq
      right; linarith
      left; linarith

    have yr : y = -2 ∨ y = -4:= by 
      have eq: y^2 + 6*y + 8 = 0 := by linarith
      have :  y^2 + 6*y + 8 = (y+4) * (y+2) := by ring
      rw [this] at eq; simp at eq
      obtain eq1 | eq2 := eq
      right; linarith
      left; linarith

    have zr : z = -1 ∨ z = 5 := by 
      have eq: z^2 - 4*z -5 = 0 := by linarith
      have : z^2 - 4*z - 5 = (z-5) * (z+1) := by ring
      rw [this] at eq; simp at eq
      obtain eq1 | eq2 := eq
      right; linarith
      left; linarith

    tauto


    --from right to left. Simple calulation for every case.
    intro sol
    rcases sol with h|h|h|h|h|h|h|h
    simp_all; norm_num
    simp_all; norm_num
    simp_all; norm_num
    simp_all; norm_num
    simp_all; norm_num
    simp_all; norm_num
    simp_all; norm_num
    simp_all; norm_num