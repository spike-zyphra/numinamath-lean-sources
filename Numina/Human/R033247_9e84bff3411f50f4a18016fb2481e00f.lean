import Mathlib

open Real

/-Given that $x$, $y$, $z$ are real numbers, and $x+y+z=3$, $xy+yz+zx=2$, find the maximum value of $z$.-/
theorem algebra_9008 :
  IsGreatest {z | ∃ x y : ℝ, x + y + z = 3 ∧ x * y + y * z + z * x = 2} (2 / (sqrt 3) + 1):= by
    constructor
    · simp
      use (1 - 1 / sqrt 3), (1 - 1 / sqrt 3)
      exact ⟨by ring_nf, by ring_nf; rw [←one_div]; simp; ring⟩
    · -- Since $x$ is a real number, the discriminant $\Delta$ of the quadratic equation in $x$ must be non-negative, i.e., $\Delta=(z-3)^2-4(z^2-3z+2)\geq0$.
      intro  z hz
      simp at hz
      obtain ⟨x, y, hz⟩ := hz
      -- From $x+y+z=3$, we get $y=3-x-z$.
      have c1 : y = 3 - x - z := by linarith
      -- Substituting this into $xy+yz+zx=2$, we obtain $x(3-x-z)+(3-x-z)z+zx=2$.
      -- Simplifying, we get $x^2+(z-3)x+(z^2-3z+2)=0$.
      have c2 : (x * x) + (z - 3) * x + (z^2 - 3 * z + 2) = 0 := by
        rw [c1] at hz
        nlinarith
      rw [show x * x = 1 * (x * x) by linarith] at c2
      have := discrim_eq_sq_of_quadratic_eq_zero c2
      simp [discrim] at this
      -- Since $x$ is a real number, the discriminant $\Delta$ of the quadratic equation in $x$ must be non-negative,
      --  i.e., $\Delta=(z-3)^2-4(z^2-3z+2)\geq0$.
      have dispos : 0 ≤ (z - 3) ^ 2 - 4 * (z ^ 2 - 3 * z + 2) := this ▸ (by positivity)
      ring_nf at dispos
      replace dispos : (z - 1)^2 ≤ 4 / 3 := by nlinarith
      -- Solving this quadratic inequality, we get z - 1 ≤ 2 / (sqrt 3).
      have c3 : z - 1 ≤ 2 / (sqrt 3) := by
        convert Real.le_sqrt_of_sq_le dispos using 1
        simp
        rw [show √4 = 2 from (sqrt_eq_iff_mul_self_eq_of_pos (by simp)).mpr (by ring)]
      linarith
