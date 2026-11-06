import Mathlib

/- Find the positive base $b$ in which the equation $13\cdot15=243$ is valid. -/
theorem number_theory_22698 {b : ℤ} (hb : b > 1) :
  (1*b+3) * (1*b+5) = (2*b^2+4*b+3) ↔ b = 6 := by
  -- (b+3)(b+5) = b^2+8b+15
  have h1: (1*b+3)*(1*b+5) = b^2+8*b+15 := by ring
  -- and b^2+8b+15 = 2b^2+4b+3 simplifies to b^2-4b-12=0
  have h2: (1*b+3) * (1*b+5) = (2*b^2+4*b+3) ↔ b^2-4*b-12=0 := by
    rw [h1]
    constructor <;> intro h
    · have: 2*b^2+4*b+3-(b^2+8*b+15) = 0 := by
        rw [h]; simp
      rw [← this]; ring
    · have: 2*b^2+4*b+3 - (b^2-4*b-12) = b^2+8*b+15 := by ring
      rw [← this, h]; simp
  -- factorize, b^2-4b-12 = (b-6)(b+2)
  have h3: b^2-4*b-12 = (b-6)*(b+2) := by ring
  -- and b > 1, so b=6 is the only possible solution.
  rw [h2, h3]
  constructor <;> intro h
  · have := mul_eq_zero.mp h
    rcases this with hp6 | hn2
    · linarith
    · have: b = -2 := by linarith [hn2]
      rw [this] at hb; norm_num at hb
  · rw [h]; simp