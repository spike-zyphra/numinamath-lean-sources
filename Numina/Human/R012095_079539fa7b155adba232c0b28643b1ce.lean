import Mathlib

/- 1. Let real numbers $x, y, z$ satisfy

$$

x+\frac{y}{z}=y+\frac{z}{x}=z+\frac{x}{y}=2 \text {. }

$$


Then $x y z=$ ( ).
(A) 3 or 7
(B) 1 or 3
(C) -3 or -7
(D) 1 or -7 -/
theorem algebra_182156 {x y z : ℝ} (h : x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0)
    (h1 : x + y / z = 2) (h2 : y + z / x = 2) (h3 : z + x / y = 2) :
    x * y * z = 1 ∨ x * y * z = -7 := by

        --Obtain z * x + y = 2 * z using h1.
        have h₁ : z * x + y = 2 * z := by
            calc
                _ = z * (x + y / z) := by
                    rw [mul_add]
                    field_simp [h.2.2]
                _ = z * 2 := by rw [h1]
                _ = 2 * z := by rw [mul_comm]


        --Obtain x * y + z = 2 * x using h2.
        have h₂ : x * y + z = 2 * x := by
            calc
                _ = x * (y + z / x) := by
                    rw [mul_add]
                    field_simp [h.1]
                _ = x * 2 := by rw [h2]
                _ = 2 * x := by rw [mul_comm]

        --Obtain y * z + x = 2 * y using h3.
        have h₃ : y * z + x = 2 * y := by
            calc
                _ = y * (z + x / y) := by
                    rw [mul_add]
                    field_simp [h.2.1]
                _ = y * 2 := by rw [h3]
                _ = 2 * y := by rw [mul_comm]

        --Obtain x * y + y * z + z * x = x + y + z.
        have h₄ : x * y + y * z + z * x = x + y + z := by linarith

        --Obtain (2 - x) * (2 - y) * (2 - z) = y / z * z / x * x / y.
        have h₅_0 : (2 - x) * (2 - y) * (2 - z) = y / z * z / x * x / y := by
            have h51 : 2 - x = y / z := by linarith
            have h52 : 2 - y = z / x := by linarith
            have h53 : 2 - z = x / y := by linarith
            rw [h51, h52, h53]
            ring

        --Obtain  y / z * z / x * x / y = 1.
        have h₅_1 : y / z * z / x * x / y = 1 := by
            have : x * (y * z) ≠ 0 := by
                apply mul_ne_zero
                exact h.1
                apply mul_ne_zero
                exact h.2.1
                exact h.2.2
            field_simp
            rw [mul_comm, mul_assoc, mul_comm z (x*y), mul_assoc]
            apply div_self
            exact this

        --Obtain (2 - x) * (2 - y) * (2 - z) = 1.
        have h₅ : (2 - x) * (2 - y) * (2 - z) = 1 := by
            rw [←h₅_1]
            exact h₅_0

        --Obtain  x * y * z = 7 - 2 * (x + y + z).
        have h₆ : x * y * z = 7 - 2 * (x + y + z) := by
            linarith

        --Show 3 * x * y * z = 4 * (x + y + z) - (x + y + z)^2.
        have h₇ : 3 * (x * y * z) = 4 * (x + y + z) - (x + y + z)^2 := by
            --show  x * y * z = 2 * y * z - y^2
            have h₇_1 : x * y * z = 2 * y * z - y^2 := by
                calc
                    _ = y * (z * x) := by rw [mul_assoc, mul_comm, mul_assoc]
                    _ = y * (2 * z - y) := by
                        have : z * x = 2 * z - y := by linarith
                        rw [this]
                    _ = 2 * y * z - y^2 := by linarith

            --x * y * z = 2 * z * x - z^2.
            have h₇_2 : x * y * z = 2 * z * x - z^2 := by
                calc
                    _ = z * (x * y) := by rw [mul_comm]
                    _ = z * (2 * x - z) := by
                        have : x * y = 2 * x - z := by linarith
                        rw [this]
                    _ = 2 * z * x - z^2 := by linarith

            --x * y * z = 2 * x * y - x^2.
            have h₇_3 : x * y * z = 2 * x * y - x^2 := by
                calc
                    _ = x * (y * z) := by rw [mul_assoc]
                    _ = x * (2 * y - x) := by
                        have : y * z = 2 * y - x := by linarith
                        rw [this]
                    _ = 2 * x * y - x^2 := by linarith

            linarith

        --Show 21 - 6 * (x + y + z) = 4 * (x + y + z) - (x + y + z)^2.
        have h₈ : 21 - 6 * (x + y + z) = 4 * (x + y + z) - (x + y + z)^2 := by linarith

        --It follows that (x + y + z - 3) * (x + y + z - 7) = 0.
        have h₉ : (x + y + z - 3) * (x + y + z - 7) = 0 := by
            linarith

        --Therefore, x + y + z - 3 = 0 ∨ x + y + z - 7 = 0.
        have h10 : x + y + z - 3 = 0 ∨ x + y + z - 7 = 0 := by
            exact mul_eq_zero.mp h₉

        --We close the goal using cases.
        by_cases
        h11 : x + y + z - 3 = 0
        have h111 : x + y + z = 3 := by linarith
        left
        linarith
        --Show x + y + z - 7 = 0.
        have :  x + y + z - 7 = 0 := by
            tauto
        right
        linarith