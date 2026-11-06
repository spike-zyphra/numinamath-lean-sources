import Mathlib

/- The quadratic $3x^2-24x+72$ can be written in the form $a(x+b)^2+c$, where $a$, $b$, and $c$ are constants. What is $a+b+c$? -/
theorem algebra_21265 {a b c : ℝ} (h : ∀ x, 3 * x ^ 2 - 24 * x + 72 = a * (x + b) ^ 2 + c) :
    a + b + c = 23 := by
    -- create the equations for x = 0, x = 1, x = -1
    have h1 := h 0
    have h2 := h 1
    have h3 := h (-1:ℝ )
    -- solve the equation
    ring_nf at h1 h2 h3
    rw [add_assoc] at h2; rw [<-h1] at h2
    rw [add_assoc] at h3; rw [<-h1] at h3
    have ha : a = 3 := by linarith
    rw [ha] at h1 h2 h3
    ring_nf at h1 h2 h3
    have hb : b = -4 := calc b = b * 6 / 6 := by ring_nf
      _ = (75 + b * 6 - 75) / 6 := by ring_nf
      _ = (51 - 75) / 6 := by rw [<-h2]
      _ = -24 / 6 := by ring_nf
      _ = -4 := by ring_nf
    rw [hb] at h1
    ring_nf at h1
    have hc : c = 24 := by linarith
    rw [ha, hb, hc]
    ring_nf
