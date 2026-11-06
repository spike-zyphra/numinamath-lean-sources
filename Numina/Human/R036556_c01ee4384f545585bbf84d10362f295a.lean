import Mathlib

/- Given $0 \leqslant x, y, z \leqslant 1$, solve the equation:
$$\frac{x}{1+y+z x}+\frac{y}{1+z+x y}+\frac{z}{1+x+y z}=\frac{3}{x+y+z} .$$ -/
theorem algebra_599067 (x y z : ℝ) (hd : x + y + z ≠ 0) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) (hz : 0 ≤ z ∧ z ≤ 1)
    (h : x / (1 + y + z * x) + y / (1 + z + x * y) + z / (1 + x + y * z) = 3 / (x + y + z)) :
    x = 1 ∧ y = 1 ∧ z = 1 := by

    obtain ⟨xpos,xle1⟩ := hx
    obtain ⟨ypos,yle1⟩ := hy
    obtain ⟨zpos,zle1⟩ := hz

    -- We will prove that x / (1+y+zx) ≤ 1 / (x+y+z) and the equlity can only happen when x = 1, and similarly for y and z.
    -- Note that 1 / (x+y+z) + 1 / (x+y+z) + 1 / (x+y+z) = 3 / (x+y+z), the right-hand size. We get that x=y=z=1.
    have : 1 / (1 + y + z * x) ≤ 1/ (x+y+z) := by 
      have : (x+y+z) ≤ (1 + y + z * x) := by 
        have : x + z ≤ z * x + 1 := by nlinarith
        linarith
      refine one_div_le_one_div_of_le ?_ this
      positivity
    have : x / (1 + y + z * x) ≤ 1 / (1 + y + z*x) := by 
      refine (div_le_div_iff_of_pos_right ?_).mpr xle1
      nlinarith
    have : x / (1 + y + z * x) ≤ 1/ (x+y+z) := by linarith

    have : 1 / (1 + z + x * y) ≤ 1/ (x+y+z) := by
      have : (x+y+z)≤ (1 + z + x * y) := by
        have : x + y ≤ x*y + 1 := by nlinarith
        linarith
      refine one_div_le_one_div_of_le ?_ this
      positivity
    have : y / (1 + z + x * y) ≤ 1 / (1 + z + x*y) := by
      refine (div_le_div_iff_of_pos_right ?_).mpr yle1
      nlinarith
    have : y / (1 + z + x * y)≤ 1/ (x+y+z) := by linarith

    have : 1 / (1 + x + y * z) ≤ 1/ (x+y+z) := by
      have : (x+y+z) ≤ (1 + x + y * z) := by
        have : y + z ≤ y*z + 1 := by nlinarith
        linarith
      refine one_div_le_one_div_of_le ?_ this
      positivity
    have : z / (1 + x + y * z) ≤ 1/(1 + x + y*z) := by
      refine (div_le_div_iff_of_pos_right ?_).mpr zle1
      positivity
    have : z / (1 + x + y * z)≤ 1/ (x+y+z) := by linarith


    have : 1/ (x+y+z) + 1/ (x+y+z) + 1/ (x+y+z) = 3 / (x+y+z) := by ring
    rw [← this] at h

    have : x / (1 + y + z * x) = 1/ (x+y+z) := by linarith
    have : x = 1 := by 
      by_contra xneq1
      have xl1 : x < 1 := by exact lt_of_le_of_ne xle1 xneq1
      have : x / (1 + y + z * x) < 1 / (1 + y + z*x) := by 
        refine (div_lt_div_iff_of_pos_right ?_).mpr xl1
        nlinarith
      linarith
    have : y = 1 := by
      by_contra yneq1
      have yl1 :  y < 1 := by exact lt_of_le_of_ne yle1 yneq1
      have :  y / (1 + z + x * y) < 1 / (1 + z + x*y) := by
        refine (div_lt_div_iff_of_pos_right ?_).mpr yl1
        nlinarith
      linarith
    have : z= 1 := by
      by_contra zneq1
      have zl1 :  z < 1 := by exact lt_of_le_of_ne zle1 zneq1
      have :  z / (1 + x + y * z) < 1 / (1 + x + y*z) := by
        refine (div_lt_div_iff_of_pos_right ?_).mpr zl1
        nlinarith
      linarith

    tauto