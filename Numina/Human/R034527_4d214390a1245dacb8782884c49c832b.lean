import Mathlib

open Real

/- For −1 < r < 1, let S(r) denote the sum of the geometric series
12+12*r+12*r^2+12*r^3+....

Let a between −1 and 1 satisfy S(a)S(−a)=2016. Find S(a)+S(−a). -/
theorem algebra_96549 {S : ℝ → ℝ} {a : ℝ} (ha : -1 < a ∧ a < 1)
(hS : ∀ r, S r = ∑' n : ℕ, 12 * r ^ n) (h : S a * S (-a) = 2016):
S a + S (-a) = 336 := by {
  -- We begin by evaluating the function S, which is essentially just a geometric sum, and converges as long as the argument
  -- is < 1 in absolute value.
  have hS' : ∀ r : ℝ, -1 < r ∧ r < 1 → S r = 12 / (1 - r) := by {
    intros r hr
    rw [hS]
    
    rw [tsum_mul_left,tsum_geometric_of_norm_lt_one]
    trivial
    simp
    rw [abs_lt]
    exact hr
  }
  -- We evaluate S a and S (-a) , which we can do because both of them are < 1 in absolute value.
  have hSa := hS' a ha
  have : -1 < -a ∧ -a < 1 := by {
    constructor
    linarith
    linarith
  }
  have hSma := hS' (-a) this
  simp at hSma
  -- Now we plug in the values of the geometric sum in our assumption and conclusion.
  rw [hSa,hSma]
  rw [hSa,hSma] at h
  -- From here we just need to do simple algebraic manipulations to deduce the claim.
  rw [div_add_div]
  ring_nf
  rw [div_mul_div_comm] at h
  ring_nf at h
  have : (24 : ℝ) = 144 / 6 := by norm_num
  rw [this,←mul_div_assoc,h]
  norm_num
  linarith
  linarith
}