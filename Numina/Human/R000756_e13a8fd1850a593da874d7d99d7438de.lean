import Mathlib
/-Given that $x$ is a multiple of $15336$, what is the greatest common divisor of $f(x)=(3x+4)(7x+1)(13x+6)(2x+9)$ and $x$?-/

theorem number_theory_4749 (x : ℕ) (hx : 15336 ∣ x) :
    x.gcd ((3 * x + 4) * (7 * x + 1) * (13 * x + 6) * (2 * x + 9)) =  216 := by 
      ring_nf
      have hx2:216 + x * 2190 + x ^ 2 * 5237 + x ^ 3 * 3515 + x ^ 4 * 546 = 216+(2190 + x*5237+x^2*3515+x^3*546)*x := by ring
      -- extract x
      rw [hx2]
      rw [Nat.gcd_add_mul_self]
      -- use hx
      rcases hx with ⟨k,hk⟩
      have hk2: x = 216*(71*k):= by linarith
      -- simp at goal
      rw [hk2]
      simp




      
      

