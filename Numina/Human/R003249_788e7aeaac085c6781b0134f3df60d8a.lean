import Mathlib

open Real

/- 3.334. $\frac{\cos 63^{\circ} \cos 3^{\circ}-\cos 87^{\circ} \cos 27^{\circ}}{\cos 132^{\circ} \cos 72^{\circ}-\cos 42^{\circ} \cos 18^{\circ}}=-\tan 24^{\circ}$. -/
theorem algebra_163946 : (cos (63 * π / 180) * cos (3 * π / 180) - cos (87 * π / 180) * cos (27 * π / 180)) /
    (cos (132 * π / 180) * cos (72 * π / 180) - cos (42 * π / 180) * cos (18 * π / 180)) = -tan (24 * π / 180) := by
  calc _ = (cos (63 * π / 180) * cos (π / 2 - 87 * π / 180) - cos (87 * π / 180) * cos (π / 2 - 63 * π / 180)) /
        (cos (π/2 - -42 * π / 180) * cos (π / 2 - 18 * π / 180) - cos (42 * π / 180) * cos (18 * π / 180)) := by ring
    _ = (cos (63 * π / 180) * sin (87 * π / 180) - cos (87 * π / 180) * sin (63 * π / 180)) /
        (sin (-42 * π / 180) * sin (18 * π / 180) - cos (42 * π / 180) * cos (18 * π / 180)) := by simp [cos_pi_div_two_sub]
    _ = ( sin (87 * π / 180) * cos (63 * π / 180) - cos (87 * π / 180) * sin (63 * π / 180)) /
        -(cos (42 * π / 180) * cos (18 * π / 180) + sin (42 * π / 180) * sin (18 * π / 180) ) := by 
      simp [neg_div]; ring
    _ = sin (24 * π / 180) / -cos (24 * π / 180) := by rw [← sin_sub, ← cos_sub]; ring
      -- we use the equalities sin(x)cos(y) - cos(x)sin(y) = sin(x-y)
      -- and cos(x)cos(y) + sin(x)sin(y) = cos(x-y)
    _ = -tan (24 * π / 180) := by rw [tan_eq_sin_div_cos]; ring