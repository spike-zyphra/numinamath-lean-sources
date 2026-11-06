import Mathlib

/- Example 4 Let $x, y, z \geqslant 0$, prove: $x(x-z)^{2}+y(y-z)^{2} \geqslant(x-z)(y-z)(x+y-z)$.

 -/
theorem inequalities_107423
    (x y z : ℝ)
    (hx : 0 ≤ x)
    (hy : 0 ≤ y)
    (hz : 0 ≤ z) :
    x * (x - z) ^ 2 + y * (y - z) ^ 2 ≥ (x - z) * (y - z) * (x + y - z) := by
  -- convert to schur's inequality
  suffices 0 ≤ x * (x - y) * (x - z) + y * (y - x) * (y - z) + z * (z - x) * (z - y) by linarith
  -- we will provide schur's inequality proof (as it's not in mathlib)
  wlog h : z ≤ y ∧ y ≤ x
  -- assume z ≤ y ≤ x, as by using total ness of ≤ we can apply the proof in all other combinations
  . obtain hxy | hxy := LinearOrder.le_total x y <;>
      obtain hxz | hxz := LinearOrder.le_total x z <;>
      obtain hyz | hyz := LinearOrder.le_total y z
    . specialize this z y x hz hy hx ⟨by linarith, by linarith⟩
      linarith
    . specialize this y z x hy hz hx ⟨by linarith, by linarith⟩
      linarith
    . specialize this y z x hy hz hx ⟨by linarith, by linarith⟩
      linarith
    . specialize this y x z hy hx hz ⟨by linarith, by linarith⟩
      linarith
    . specialize this z x y hz hx hy ⟨by linarith, by linarith⟩
      linarith
    . specialize this z x y hz hx hy ⟨by linarith, by linarith⟩
      linarith
    . specialize this x z y hx hz hy ⟨by linarith, by linarith⟩
      linarith
    . specialize this x y z hx hy hz ⟨by linarith, by linarith⟩
      linarith
  -- now convert rhs to following format
  . convert_to 0 ≤ (x-y) * (x * (x - z) - y * (y - z)) + z * (x - z) * (y - z)
    . ring
    -- the expressions are positivity due to assumed order
    apply add_nonneg
    . apply mul_nonneg
      . linarith
      . nlinarith
    . repeat apply mul_nonneg
      . assumption
      . linarith
      . linarith