import Mathlib

/-
Let $x, y$, and $z$ be distinct real numbers that sum to 0 . Find the maximum possible value of

$$
\frac{x y+y z+z x}{x^{2}+y^{2}+z^{2}} .
$$
-/
theorem algebra_611306 (x y z: ℝ) (h: x + y + z = 0) (hd: x ≠ y ∧ y ≠ z ∧ z ≠ x) : (x*y + y*z + z*x)/(x^2 + y^2 + z^2) =  -1 / 2 := by
  have hp: x^2 + y^2 + z^2 > 0 := by

    -- $x^2+y^2+z^2>0$ since $x,y,z$ are distinct.
    by_contra! hc

    -- use contra to prove they are equal, which is a contradiction.
    have hlt: x^2 + y^2 + z^2 ≥ 0 := by
      apply add_nonneg;
      apply add_nonneg; 
      exact sq_nonneg x; exact sq_nonneg y; exact sq_nonneg z
    have hq: x^2 + y^2 + z^2 = 0 := by
      linarith only [hc,hlt]

    -- if x^2+y^2+z^2=0, then x=y=z=0.
    have hx : x^2 ≤ 0 := by 
      calc
        _ = -(y^2 + z^2) := by linarith
        _ ≤ 0 := by
          have : 0 ≤ y^2 + z^2 := by exact add_nonneg (sq_nonneg y) (sq_nonneg z)
          linarith
    have hx0: x = 0 := by
      have ht1: x^2 = 0 := le_antisymm hx (sq_nonneg x)
      rw [pow_eq_zero_iff] at ht1
      linarith
      linarith
    have hy : y^2 ≤ 0 := by 
      calc
        _ = -(x^2 + z^2) := by linarith
        _ ≤ 0 := by
          have : 0 ≤ x^2 + z^2 := by exact add_nonneg (sq_nonneg x) (sq_nonneg z)
          linarith
    have hy0: y = 0 := by
      have ht1: y^2 = 0 := le_antisymm hy (sq_nonneg y)
      rw [pow_eq_zero_iff] at ht1
      linarith
      linarith
    
    -- conlusion x=y=0 contradicts with x≠y and y≠z.
    have heq: x = y := by linarith
    tauto
  
  -- The final goal is reduced to solve
  have h1: x*y + y*z + z*x = -1/2 * (x^2 + y^2 + z^2) := by
    calc
      -- the  core idenities used here are:
      _ = x*y + y*z + z*x + 1/2 * (x^2 + y^2 + z^2) - 1/2 * (x^2 + y^2 + z^2) := by ring
      _ = 1/2*(x + y + z)^ 2 - 1/2 * (x^2 + y^2 + z^2) := by ring
      _ = 1/2 * 0^2 - 1/2 * (x^2 + y^2 + z^2) := by rw [h]
      _ = -1/2 * (x^2 + y^2 + z^2) := by ring
  rw [h1]
  field_simp
  ring_nf
    

      
