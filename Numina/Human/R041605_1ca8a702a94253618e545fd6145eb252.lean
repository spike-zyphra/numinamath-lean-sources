import Mathlib

/- Find all solutions to the equation $\displaystyle\sqrt[3]{3 - x} = -\frac{3}{2}$. -/
theorem algebra_10341 (x : ℝ) :
  let cbrt x := if x ≥ 0 then x ^ (1 / 3 : ℝ) else -(-x) ^ (1 / 3 : ℝ)
  cbrt (3 - x) = -3 / 2 ↔ x = 51 / 8 := by

  -- Note that Lean does not have a suitable definition of cube root on ℝ, so we need to define it manually.
  -- We define cbrt x to be x ^ (1 / 3) if x ≥ 0 and -(-x) ^ (1 / 3) if x < 0.

  -- Lemma: cbrt x ^ 3 = x for all x.
  have H {x : ℝ} : (fun x ↦ if x ≥ 0 then x ^ (1 / 3 : ℝ) else -(-x) ^ (1 / 3 : ℝ)) x ^ 3 = x := by
    -- We do casework on whether x is nonnegative.
    by_cases h : x ≥ 0
    . -- If x is nonnegative, then cbrt x = x ^ (1 / 3).
      simp [h]
      -- x ^ (1 / 3) ^ 3 = x ^ (1/3 * 3) = x.
      rw [← Real.rpow_mul_natCast h]
      simp
    . -- If x is negative, then cbrt x = -(-x) ^ (1 / 3).
      simp [h]
      -- (-(-x) ^ (1 / 3)) ^ 3 = (-x) ^ (1 / 3 * 3) = -x.
      rw [Odd.neg_pow (show Odd 3 by decide)]
      -- (-x) ^ (1 / 3 * 3) = -x.
      rw [← Real.rpow_mul_natCast (show -x ≥ 0 by linarith)]
      simp

  -- Now we solve the actual problem.
  constructor <;> intro h
  . -- If cbrt (3 - x) = -3 / 2, then (3 - x) = (-3 / 2) ^ 3.
    apply_fun (· ^ 3) at h
    rw [H] at h
    -- Thus x = 3 - (-3 / 2) ^ 3 = 51 / 8
    linarith
  . -- If x = 51 / 8, then cbrt (3 - x) = - cbrt 27 / 8 = -3 / 2.
    subst x
    norm_num
    -- Show that 27 / 8 = (3 / 2) ^ 3.
    rw [show (27 : ℝ) / 8 = (3 / 2) ^ 3 by norm_num]
    rw [← Real.rpow_natCast_mul (by norm_num)]
    simp
