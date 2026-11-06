import Mathlib

/- 19. Suppose $x, y, z$ and $\lambda$ are positive real numbers such that

$$

\begin{aligned}
y z & =6 \lambda x \\
x z & =6 \lambda y \\
x y & =6 \lambda z \\
x^{2}+y^{2}+z^{2} & =1
\end{aligned}

$$


Find the value of $(x y z \lambda)^{-1}$. -/
theorem algebra_101399 (x y z lambda : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hlambda : 0 < lambda)
    (h1 : y * z = 6 * lambda * x) (h2 : x * z = 6 * lambda * y) (h3 : x * y = 6 * lambda * z)
    (h4 : x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    (x * y * z * lambda)⁻¹ = 54
  := by
    -- Multiply the first three equations with x, y and z respectively.
    apply_fun (fun a => x * a) at h1
    apply_fun (fun a => y * a) at h2
    apply_fun (fun a => z * a) at h3
    ring_nf at h1
    ring_nf at h2
    ring_nf at h3

    -- Then we have x^2 * lamda * 6 = y^2 * lambda * 6 = z^2 * lambda * 6
    have h5 : x ^ 2 * lambda * 6 = y ^ 2 * lambda * 6 := by { rw [← h1, ← h2]; ring }
    have h6 : x ^ 2 * lambda * 6 = z ^ 2 * lambda * 6 := by { rw [← h1, ← h3]; ring }

    -- We have that lambda ≠ 0
    by_cases h : lambda = 0
    · exact ((lt_self_iff_false 0).mp (h ▸ hlambda)).elim

    simp only [mul_eq_mul_right_iff, h, or_false, OfNat.ofNat_ne_zero] at h5
    simp only [mul_eq_mul_right_iff, h, or_false, OfNat.ofNat_ne_zero] at h6

    -- Square root of a square is identity
    have square_sqrt : ∀ {x}, 0 < x -> √(x ^ 2) = x
    · intro x hx
      rw [Real.sqrt_eq_rpow, ←Real.rpow_natCast, ←Real.rpow_mul (le_of_lt hx)]
      simp only [Nat.cast_ofNat, one_div, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, IsUnit.mul_inv_cancel, Real.rpow_one]

    -- We have that x = y
    have x_eq_y : x = y
    · apply_fun Real.sqrt at h5
      rw [square_sqrt hx, square_sqrt hy] at h5
      exact h5

    -- And that x = z
    have x_eq_z : x = z
    · apply_fun Real.sqrt at h6
      rw [square_sqrt hx, square_sqrt hz] at h6
      exact h6

    -- Replace every z and y with x
    subst x_eq_y
    subst x_eq_z
    ring_nf at h4

    -- Then we know that x = (√3)⁻¹
    have x_eq : x = (√3)⁻¹
    · apply_fun (fun x => x / 3) at h4
      rw [mul_div_cancel_right₀] at h4
      apply_fun Real.sqrt at h4
      rw [square_sqrt hx, one_div, Real.sqrt_inv] at h4
      exact h4
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]

    -- Then we can simplify
    rw [x_eq] at h1
    field_simp at h1
    ring_nf at h1

    -- Then we know the value of lambda
    have l_eq : lambda = 3 / (√3 * 18)
    · nth_rw 1 [h1]
      ring_nf
      field_simp

    -- Then we can show the final equality
    rw [l_eq, x_eq]
    field_simp
    ring_nf
    rw [Real.sqrt_eq_rpow, ←Real.rpow_natCast, ←Real.rpow_mul]
    ring_nf
    exact zero_le_three