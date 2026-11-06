import Mathlib

/- 6. In the field of real numbers, solve the system of equations

$$
\begin{aligned}
& x^{4}+y^{2}+4=5 y z, \\
& y^{4}+z^{2}+4=5 z x, \\
& z^{4}+x^{2}+4=5 x y .
\end{aligned}
$$

(Jaroslav Švrček) -/
theorem algebra_265305 (x y z : ℝ) :
    x ^ 4 + y ^ 2 + 4 = 5 * y * z ∧ y ^ 4 + z ^ 2 + 4 = 5 * z * x ∧ z ^ 4 + x ^ 2 + 4 = 5 * x * y ↔
    (x = Real.sqrt 2 ∧ y = Real.sqrt 2 ∧ z = Real.sqrt 2) ∨
    (x = -Real.sqrt 2 ∧ y = -Real.sqrt 2 ∧ z = -Real.sqrt 2) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    -- By using $(x²-2)² \ge 0$ e.t.c, and combine the system of equations. 
    -- Then we will get 
    -- $$ (x-y)^{2}+(y-z)^{2}+(z-x)^{2} = 0 . $$
    have h4 : (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x ^ 2 - 2), sq_nonneg (y ^ 2 - 2), sq_nonneg (z ^ 2 - 2), h1, h2, h3]
    -- Hence, $x = y = z.$
    have hxyz : x = y ∧ y = z := by 
      constructor <;> nlinarith only [h4]
    rcases hxyz with ⟨hxy, hyz⟩
    -- By $z^4+z²+4=5z², z²=2$
    have hz2 : z ^ 2 = 2 := by
      rw [hxy, hyz] at h1
      nlinarith [h1] 
    -- i.e $z= \sqrt2 $ or $z=-\sqrt2$
    rw [show 2 = √2 ^ 2 by rw [Real.sq_sqrt (by norm_num)]] at hz2
    rw [sq_eq_sq_iff_eq_or_eq_neg] at hz2 
    -- So $x=y=z=\sqrt2$ or $x=y=z=-\sqrt2$
    subst hyz hxy
    simp_all
  -- Verification is easy
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    repeat 
      ring_nf
      rw [show √2 ^ 4 = (√ 2 ^ 2) * (√2 ^ 2) by ring]
      simp only [Nat.ofNat_nonneg, Real.sq_sqrt, and_self]
      norm_num 

