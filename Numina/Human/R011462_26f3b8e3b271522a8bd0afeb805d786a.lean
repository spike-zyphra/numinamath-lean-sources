import Mathlib

/-
If $x$ and $y$ are real numbers, and ${{\left( x-1 \right)}^{2018}}+\left| y+2 \right|=0$, find the value of $3x-2y$.

-/

theorem algebra_633719 (x y: ℝ) (h : (x-1)^2018 + |y+2| = 0):
3*x - 2*y = 7 := by
  have h1 : 0 ≤ (x - 1) ^ 2018:= by positivity
  have h2 : 0 ≤ |y+2| := by positivity

  --Since these two terms are always non-negative, they must both be zero.
  --Then we get the value of x and y.
  have xe : x = 1 := by 
    have eq: (x-1)^2018 = 0 := by
      by_contra ne
      push_neg at ne
      have g: 0 < (x-1)^2018 := by exact lt_of_le_of_ne h1 (id (Ne.symm ne))
      have : 0 < (x-1)^2018 + |y+2| := by exact Right.add_pos_of_pos_of_nonneg g h2
      rw [h] at this
      norm_num at this
    have : x-1 = 0 := by apply pow_eq_zero at eq; exact eq
    have : x=1 := by linarith only [this]
    exact this
    
  have ye : y = -2:= by
    have : |y+2| = 0 := by 
      by_contra ne
      push_neg at ne
      have g : 0 <  |y+2| := by exact lt_of_le_of_ne h2 (id (Ne.symm ne))
      have : 0 < (x-1)^2018 + |y+2| := by exact add_pos_of_nonneg_of_pos h1 g
      rw [h] at this
      norm_num at this
    have : y + 2 = 0 := by exact abs_eq_zero.mp this
    have : y = -2 := by linarith only [this]
    exact this

  simp [xe,ye]
  norm_num
