import Mathlib

/- 13.402 The capacities of three vessels $A$, B, C, each of which has the shape of a cube, are in the ratio $1: 8: 27$, and the volumes of water poured into them are in the ratio 1:2:3. After transferring part of the water from vessel A to vessel B and from vessel B to vessel C, the water level in all three vessels became the same. Then, $128 \frac{4}{7}$ liters of water were transferred from vessel C to vessel B, and after that, from vessel B to vessel A, so that the water depth in vessel A became twice that in vessel B. As a result, it turned out that there was now $100$ liters less water in vessel A than there was initially. How much water was there initially in each vessel? -/
theorem algebra_199491 {a x y z : ℝ} (hpos : a > 0)
  -- volumes after first transfer
  (h₁ : (x - y) / a^2 = (2 * x + y - z) / (2 * a)^2)
  (h₁' : (2 * x + y - z) / (2 * a)^2 = (3 * x + z) / (3 * a)^2)
  -- volume after second transfer
  (h₂ : (x - y + 128 + 4/7) / a^2 = 2 * (2 * x + y - z) / (2 * a)^2)
  (h₃ : (x - y + 128 + 4/7) + 100 = x) : x = 500 := by
  -- find volume z from equation 1
  rw [div_eq_div_iff (by positivity) (by positivity), mul_pow, ←mul_assoc] at h₁
  apply mul_right_cancel₀ (by positivity) at h₁
  have hz : z = -2 * x + 5 * y := by linarith [h₁]
  rw [hz] at h₁' h₂
  -- find volume y from equation 2
  rw [div_eq_div_iff (by positivity) (by positivity), mul_pow, mul_pow, ←mul_assoc, ←mul_assoc] at h₁'
  apply mul_right_cancel₀ (by positivity) at h₁'
  ring_nf at h₁'
  have hy : y = 4/7 * x := by linarith [h₁']
  rw [hy] at h₂
  rw [div_eq_div_iff (by positivity) (by positivity), mul_pow, ←mul_assoc, ←mul_assoc] at h₂
  apply mul_right_cancel₀ (by positivity) at h₂
  -- conclude using equation 3
  linarith