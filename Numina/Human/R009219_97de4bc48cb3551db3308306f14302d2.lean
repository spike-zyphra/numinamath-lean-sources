import Mathlib

/- Determine the largest integer $n$ such that $7^{2048}-1$ is divisible by $2^{n}$. -/
theorem algebra_608199 :
    padicValNat 2 (7 ^ 2048 - 1) = 14 := by
  -- Note on formalization:
  -- the p-adic valuation of a natural n ≠ 0 is the largest natural number k such that p^k divides n

  -- We use the Lifting The Exponent Lemma:
  -- v_2(a^n - b^n) = v_2(a + b) + v_2(a - b) + v_2(n) - 1 for a, b odd, n positive and even
  have h := padicValNat.pow_two_sub_pow (show 1 < 7 by decide) (show 2 ∣ 7 - 1 by decide) (show ¬2 ∣ 7 by decide) (show 2048 ≠ 0 by decide) (show Even 2048 by decide)
  rw [show 1 ^ 2048 = 1 by simp] at h
  -- Calculate the RHS
  rw [← Nat.add_one_sub_one (padicValNat _ _),
      h,
      show padicValNat 2 (7 + 1) = 3 by native_decide,
      show padicValNat 2 (7 - 1) = 1 by native_decide,
      show padicValNat 2 2048 = 11 by native_decide]
