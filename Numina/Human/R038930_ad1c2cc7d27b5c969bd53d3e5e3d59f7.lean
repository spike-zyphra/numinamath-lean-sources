import Mathlib

/- 3. The teacher wrote on the board the fraction $\frac{a n+b}{c n+d}$ (numbers $a, b, c, d, n$ are natural). Vova was able to reduce the fraction (numerator and denominator) by 2017. Prove that then $a d - b c$ is divisible by 2017. -/
theorem number_theory_101312 {a b c d n : ℕ} (h1 : 2017 ∣ a * n + b) (h2 : 2017 ∣ c * n + d) :
  2017 ∣ a * d - b * c
:= by
  rcases h1 with ⟨k1, h1⟩
  rcases h2 with ⟨k2, h2⟩
  
  -- We can rewrite a * d - b * c = a * (c * n + d) - c * (a * n + b)
  have : a * d - b * c = a * (c * n + d) - c * (a * n + b) := by
    ring_nf
    omega
  rw [this]
  clear this

  rw [h1, h2]
  ring_nf
  rw [show a * k2 * 2017 - c * k1 * 2017 = (a * k2 - c * k1) * 2017 by omega]
  omega