import Mathlib

/- The quadratic $4x^2+2x-1$ can be written in the form $a(x+b)^2+c$, where $a$, $b$, and $c$ are constants. What is $a+b+c$? -/
theorem algebra_19385 {a b c : ℝ} (h : ∀ x, 4 * x ^ 2 + 2 * x - 1 = a * (x + b) ^ 2 + c) :
    a + b + c = 3 := by
        -- 将 x = -1, 0, 1代入，得到三个方程
        have h1 := h 0
        have h2 := h (-1)
        have h3 := h 1
        ring_nf at h1 h2 h3
        replace h2 : 2 = a - a * b * 2:= by linarith
        replace h3 : 6 = a + a * b * 2:= by linarith
        replace h2 : a = 4:= by linarith
        rw [h2] at h3
        replace h3 : b = 1 / 4:= by linarith
        rw [h2, h3] at h1
        linarith
