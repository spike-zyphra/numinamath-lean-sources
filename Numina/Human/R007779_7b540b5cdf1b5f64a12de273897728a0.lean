import Mathlib


/-
The function $f(x)= \dfrac {2^{x}+a}{2^{x}-a}$ is an odd function. Determine the value of the real number $a$.
-/

theorem algebra_9127
    {a : ℝ}
    (f : ℝ → ℝ)
    (hf : f = fun x => (2^x + a) / (2^x - a)) :
    (∀ x, f (-x) = - f x) ↔ a = 1 ∨ a = -1 := by

  -- some auxiliary lemmas for computation
  have r_2powne0 : ∀ x : ℝ, x ≠ 0 →  (2 : ℝ) ^ x ≠ 0 := by
    intro x hx
    refine (Real.rpow_ne_zero ?hc.hx hx).mpr ?_
    all_goals linarith

  have r1 : ∀ (x : ℝ), x ≠ 0 → ((2 : ℝ) ^ (-x) + 1) / (2 ^ (-x) - 1) = -((2 ^ x + 1) / (2 ^ x - 1)) := by
    intro x hx
    calc ((2:ℝ) ^ (-x) + 1) / (2 ^ (-x) - 1)
      _ = ((2 ^ (-x) + 1) * (2 ^ x)) / ((2 ^ (-x) - 1) * (2 ^ x)) := by
        refine (mul_div_mul_right (2 ^ (-x) + 1) (2 ^ (-x) - 1) ?_).symm
        refine (Real.rpow_ne_zero ?hc.hx hx).mpr ?_
        all_goals linarith
      _ = (1 + 2 ^ x) / (1 - 2 ^ x) := by
        rw [← mul_neg_one, Real.rpow_mul (by norm_num), Real.rpow_neg_one,
            add_mul, sub_mul, one_mul, inv_mul_cancel₀ (r_2powne0 x hx)]
      _ = (2 ^ x + 1) / (-1 * (2 ^ x - 1)) := by ring
      _ = -((2 ^ x + 1) / (2 ^ x - 1)) := by
        rw [div_mul_eq_div_div]
        conv => lhs; rw [← inv_neg_one, div_inv_eq_mul, mul_comm, mul_div_assoc, neg_one_mul]

  have r2 : ∀ (x : ℝ), x ≠ 0 → ((2 : ℝ) ^ (-x) + -1) / (2 ^ (-x) - -1) = -((2 ^ x + -1) / (2 ^ x - -1)) := by
    intro x hx
    rw [← mul_div_mul_right (2 ^ (-x) + -1) (2 ^ (-x) - -1) (r_2powne0 x hx),
        ← mul_neg_one, Real.rpow_mul (by norm_num), Real.rpow_neg_one,
            add_mul, sub_mul, inv_mul_cancel₀ (r_2powne0 x hx), mul_comm]
    ring

  -- main part
  constructor
  . intro h
    -- let x = 0
    specialize h 0
    simp [hf] at h
    rcases eq_or_ne a 1 with ha | ha
    -- a = 1
    . left
      exact ha
    -- a ≠ 1 → a = -1
    . right
      have r : 1 - a ≠ 0 := by exact sub_ne_zero_of_ne ha.symm
      rw [← neg_one_mul, ← mul_div_assoc] at h
      apply (eq_div_iff r).mp at h
      rw [div_mul_cancel₀ _ r, neg_one_mul] at h
      linarith [eq_zero_of_neg_eq h.symm]

  . intro ha x
    rcases ha with ha | ha
    . rcases eq_or_ne x 0 with hx | hx
      . simp [ha, hf, hx]
      . simp only [ha, hf, r1 x hx]
    . rcases eq_or_ne x 0 with hx | hx
      . simp [ha, hf, hx]
      . simp only [ha, hf, r2 x hx]
