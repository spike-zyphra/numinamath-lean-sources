import Mathlib 

/-Soit $x, y$ et $z$ trois nombres réels tels que $x^{2}+y^{2}+z^{2}=1$. Trouver les valeurs minimale et maximale possibles du nombre réel $x y+y z-z x$.-/
theorem algebra_91063 : IsGreatest {k | ∃ x y z : ℝ, x^2 + y^2 + z^2 = 1 ∧ k = x*y + y*z -z*x} (1/2)
  ∧ IsLeast {k | ∃ x y z : ℝ, x^2 + y^2 + z^2 = 1 ∧ k = x*y + y*z -z*x} (-1) := by 
    constructor 
    · constructor 
      --  when $x=y=1 / \sqrt{2}$ and $z=0$. we have $x y+y z-x z=1 / 2$
      · simp
        use 1/(Real.sqrt 2), 1/(Real.sqrt 2), 0
        simp
        norm_num [←pow_two]
      · simp [upperBounds]
        intro k x y z h₁ h₂ 
        -- Based on the identity
        -- $$
        -- (x-y+z)^{2}=x^{2}+y^{2}+z^{2}-2(x y+y z-z x)=1-2(x y+y z-z x),
        -- $$
        have h1 : (x - y + z)^2 = 1 - 2*(x*y + y*z - z*x) := by nlinarith
        --  First, since $(x-y+z)^{2} \geqslant 0$, with equality when $x=y=1 / \sqrt{2}$ and $z=0$, we have
        -- $$
        -- x y+y z-z x=\frac{1-(x-y+z)^{2}}{2} \leqslant \frac{1}{2}
        -- $$
        have h2 : 0 ≤ 1 - 2*(x*y + y*z - z*x) := h1 ▸ (by positivity)
        linarith
    · constructor
      · simp 
        -- when $x=-y=z=1 / \sqrt{3}$, we have $x y+y z-x z=-1$
        use 1/(Real.sqrt 3), -1/(Real.sqrt 3), 1/(Real.sqrt 3)
        simp [div_pow]
        norm_num
        ring_nf
        norm_num
      · simp [lowerBounds]
        intro k x y z h₁ h₂
        have h1 : (x - y + z)^2 = 1 - 2*(x*y + y*z - z*x) := by nlinarith
        -- $$
        -- (x-y+z)^{2} \leqslant\left(x^{2}+y^{2}+z^{2}\right) \times\left(1^{2}+(-1)^{2}+1^{2}\right)=3,
        -- $$
        have h2 : (x - y + z)^2 ≤ 3 := by 
          rw [h1]
          have c1 : -2 * x*y ≤ x^2 + y^2 := by 
            have := two_mul_le_add_sq (-x) y 
            linarith
          have c2 : -2 * y*z ≤ y^2 + z^2 := by
            have := two_mul_le_add_sq (-y) z
            linarith
          have c3 : 2 * z*x ≤ z^2 + x^2 := two_mul_le_add_sq z x
          linarith
        -- Therefore, we have
        -- $$
        -- (x y+y z-z x)=\frac{1-(x-y+z)^{2}}{2} \geqslant \frac{1-3}{2}=-1
        -- $$
        linarith
    