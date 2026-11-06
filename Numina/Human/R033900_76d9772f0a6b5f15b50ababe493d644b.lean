import Mathlib

/-Given the equations $3x+y=17,5y+z=14$ and $3x+5z=41$, what is the value of the sum $x+y+z$?-/
theorem algebra_935 (x y z : ℝ) (h₀ : 3 * x + y = 17) (h₁ : 5 * y + z = 14) (h₂ : 3 * x + 5 * z = 41) :
    x + y + z = 12 := by
    --Sum all three equations to find that $6x+6y+6z=17+14+41$, from which $x+y+z=72/6=\boxed{12}$.
    have h :  3 * x + y + (5 * y + z) + (3 * x + 5 * z) = 17 + 14 +41 := by
      rw [h₀];rw [h₁]; rw [h₂]
    ring_nf at h
    have e := congrArg ( fun (n) => ((n) / 6 ) ) h ; simp at e; ring_nf at e
    rw [e]