import Mathlib

open Real Set

/- Let $x, y, z \in (0, \infty)$. Prove that
\[
\arctan x + \arctan y + \arctan z < \pi \iff xyz < x + y + z
\] -/
theorem inequalities_4946 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    arctan x + arctan y + arctan z < π ↔ x * y * z < x + y + z := by
  -- Lemma 0: arctan z < π / 2
  have h₀ := arctan_lt_pi_div_two z
  -- Casework on the sign of x * y - 1
  obtain h | h | h := lt_trichotomy (x * y) 1
  . -- First case: x * y < 1
    -- We have arctan x + arctan y < π / 2
    have h₁ := arctan_add_arctan_lt_pi_div_two h
    -- So both sides of this biimplication are true
    exact iff_of_true (by linarith) (by nlinarith)
  . -- Second case: x * y = 1
    -- Rewrite y = x⁻¹
    obtain rfl := inv_eq_of_mul_eq_one_right h
    -- Rewrite arctan x⁻¹ = π / 2 - arctan x
    rw [h, arctan_inv_of_pos hx]
    -- Both sides are true
    exact iff_of_true (by linarith) (by linarith)
  . -- Third case: x * y > 1
    -- Rewrite arctan x + arctan y = arctan ((x + y) / (1 - x * y)) + π
    rw [arctan_add_eq_add_pi h hx]
    calc arctan ((x + y) / (1 - x * y)) + π + arctan z < π
      _ ↔ arctan ((x + y) / (1 - x * y)) < -arctan z := by constructor <;> (intro; linarith) -- Both implication is linear
      _ ↔ arctan ((x + y) / (1 - x * y)) < arctan (-z) := by rw [arctan_neg z] -- arctan is an odd function
      _ ↔ (x + y) / (1 - x * y) < -z := arctan_strictMono.lt_iff_lt -- Strict monotonicity of arctan
      _ ↔ -z * (1 - x * y) < x + y := div_lt_iff_of_neg (by linarith) -- Cancel the denominator
      _ ↔ x * y * z < x + y + z := by constructor <;> (intro; linarith) -- Both implication is linear
