import Mathlib

/- Find all integer solutions of the equation:

$$
x^{2}+y^{2}=3\left(u^{2}+v^{2}\right)
$$ -/
theorem number_theory_165219 :
    {(x, y, z, w) : ℤ × ℤ × ℤ × ℤ | x^2 + y^2 = 3 * (z^2 + w^2)} = {(0, 0, 0, 0)} := by
  ext ⟨x, y, z, w⟩
  simp only [Set.mem_setOf_eq, Prod.mk_zero_zero, Set.mem_singleton_iff, Prod.mk_eq_zero]
  constructor
  -- Verify that (0, 0, 0, 0) is a solution.
  swap
  {
    rintro ⟨rfl, rfl, rfl, rfl⟩
    simp
  }
  -- Show that any solution must be (0, 0, 0, 0).
  intro h
  -- We want to show that by infinite descent.
  -- We use second induction on the sum of the absolute values of the components.
  obtain ⟨k, hk⟩ : ∃ k, k = x.natAbs + y.natAbs + z.natAbs + w.natAbs := ⟨_, rfl⟩
  induction k using Nat.strongRecOn generalizing x y z w with
  | ind k ih =>
    -- Assume that any solution with smaller sum of absolute values must be x = y = z = w = 0.
    -- If otherwise,
    by_contra hc
    -- We first show that 3 divides x and y, and obtain x' and y' such that x = 3 * x' and y = 3 * y'.
    obtain ⟨⟨x', rfl⟩, ⟨y', rfl⟩⟩ : 3 ∣ x ∧ 3 ∣ y := by
      replace h : x^2 + y^2 ≡ 0 [ZMOD 3] := by
        simp [Int.ModEq, h]
      -- We consider the possible values of x and y modulo 3.
      mod_cases hx : x % 3 <;> mod_cases hy : y % 3
      -- If x and y are both divisible by 3, then we are done.
      . simp only [Int.modEq_zero_iff_dvd] at hx hy
        exact ⟨hx, hy⟩
      -- Otherwise,
      all_goals
        -- We compute x ^ 2 + y ^ 2 modulo 3.
        have H := (Int.ModEq.pow 2 hx).add (Int.ModEq.pow 2 hy)
        -- We show that this is not 0 modulo 3.
        apply h.symm.trans at H
        absurd H
        decide
    -- So z^2 + w^2 = 3 * (x'^2 + y'^2).
    replace h : z^2 + w^2 = 3 * (x'^2 + y'^2) := by linarith only [h]
    -- (z, w, x', y') is a solution with smaller sum of absolute values.
    have hm : x'.natAbs + y'.natAbs + z.natAbs + w.natAbs < k := by
      simp only [hk, Int.natAbs_mul, Int.reduceAbs, add_lt_add_iff_right]
      -- It suffices to show that x' or y' is not 0.
      suffices x'.natAbs ≠ 0 ∨ y'.natAbs ≠ 0 by omega
      by_contra! H
      simp only [Int.natAbs_eq_zero] at H
      simp only [H, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
        mul_zero] at h
      obtain ⟨hz, hw⟩ : z ^ 2 = 0 ∧ w ^ 2 = 0 := by
        constructor <;>
        linarith [sq_nonneg z, sq_nonneg w]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff] at hz hw
      simp [H, hz, hw] at hc
    -- By the induction hypothesis, x' = y' = z = w = 0.
    -- We are done.
    specialize ih (x'.natAbs + y'.natAbs + z.natAbs + w.natAbs) hm z w x' y' h (by ac_rfl)
    simp [ih] at hc
