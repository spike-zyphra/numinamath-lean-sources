import Mathlib

open Real

/- Determine all numbers $x, y$ and $z$ satisfying the system of equations
$$\begin{cases} x^2 + yz = 1 \\ y^2 - xz = 0 \\ z^2 + xy = 1\end{cases}$$ -/
theorem algebra_87894 :
  {(x, y, z) : ℝ × ℝ × ℝ | x^2 + y * z = 1 ∧ y^2 - x * z = 0 ∧ z^2 + x * y = 1} =
  {(√2 / 2, √2 / 2, √2 / 2), (-√2 / 2, -√2 / 2, -√2 / 2)}:= by
  ext ⟨x,y,z⟩
  constructor
  · -- Forward direction
    intro h1
    rcases h1 with ⟨h11, h12, h13⟩
    -- We can express z in terms of x using the first equation and the third equation.
    have h21 : x = z := by nlinarith
    simp only [h21] at h11 h12
    -- We can express y in terms of z using h11 and h12.
    have h23 : y = z := by nlinarith
    simp only [h23] at h11
    simp_all
    -- We have x = y = z. So we have z ^ 2 = 1 / 2.
    have h24 : z ^ 2 = (√2 / 2) ^ 2 :=by
      rw [div_pow]
      rw [Real.sq_sqrt]
      norm_num
      linarith
      linarith
    -- Then we can conclude that z = ±√2 / 2.
    rw [pow_eq_pow_iff_of_ne_zero] at h24 <;> try nlinarith
    simp_all
    rw [neg_div]
    exact h24
  · -- Backward direction
    intro h2
    rcases h2 with ⟨rfl,rfl,rfl⟩
    · -- Case 1: x = y = z = √2 / 2
      simp
      ring_nf
      norm_num
    · -- Case 2: x = y = z = -√2 / 2
      simp_all
      ring_nf
      norm_num
