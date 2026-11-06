import Mathlib

/- 1. For positive numbers $x, y, z$, the equality


$$

\frac{x^{2}}{y}+\frac{y^{2}}{z}+\frac{z^{2}}{x}=\frac{x^{2}}{z}+\frac{z^{2}}{y}+\frac{y^{2}}{x}

$$


is satisfied. Prove that at least two of the numbers $x, y, z$ are equal to each other. -/
theorem algebra_281583 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x^2 / y + y^2 / z + z^2 / x = x^2 / z + z^2 / y + y^2 / x) :
    x = y ∨ y = z ∨ x = z
  := by
    apply_fun (fun a => x*y*z*a) at h
    rw [mul_add, mul_add, mul_add, mul_add] at h
    convert_to z * x ^ 3 + x * (y ^ 3) + y * (z ^ 3)
      = y * (x ^ 3) + x * (z ^ 3) + z * (y ^ 3) at h
    · field_simp
      ring_nf
    · field_simp
      ring_nf

    -- Reorder
    have h : z * x ^ 3 - y * (x ^ 3) + x * (y ^ 3) - z * (y ^ 3) + y * (z ^ 3) - x * (z ^ 3) = 0
    · linarith

    -- Then we factor it
    convert_to (x - y) * (x - z) * (z - y) * (x + y + z) = 0 at h
    · linarith

    -- Then at least one of the factors is zero
    simp only [mul_eq_zero] at h
    rcases h with ⟨⟨ha1 | ha2⟩ | ha3⟩ | hb
    · exact Or.inl <| sub_eq_zero.mp ha1
    · exact Or.inr <| Or.inr <| sub_eq_zero.mp ha2
    · exact Or.inr <| Or.inl <| sub_eq_zero.mp ha3 |> Eq.symm
    -- `x + y + z` can't be zero
    · linarith