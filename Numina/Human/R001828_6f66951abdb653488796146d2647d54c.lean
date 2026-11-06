import Mathlib

/- Let $x, y, z$ be three real distinct numbers such that
$$\begin{cases} x^2-x=yz \\ y^2-y=zx \\ z^2-z=xy \end{cases}$$ Show that $-\frac{1}{3} < x,y,z < 1$. -/
theorem inequalities_37795 (x y z : ℝ) (hx : x ≠ y) (hy : y ≠ z) (hz : x ≠ z)
    (h1 : x^2 - x = y * z) (h2 : y^2 - y = z * x) (h3 : z^2 - z = x * y) :
    -1 / 3 < x ∧ x < 1 ∧ -1 / 3 < y ∧ y < 1 ∧ -1 / 3 < z ∧ z < 1 := by
  refine' ⟨_, _, _, _, _, _⟩ <;> 
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hx), 
      sq_pos_of_ne_zero (sub_ne_zero.mpr hy), 
      sq_pos_of_ne_zero (sub_ne_zero.mpr hz)]