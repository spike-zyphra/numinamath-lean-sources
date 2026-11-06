import Mathlib

/- Suppose that $a$ and $b$ are integers such that   $$3b = 8 - 2a.$$How many of the first six positive integers must be divisors of $2b + 12$? -/
theorem number_theory_16468 :
    {x : ℤ | x ∈ Finset.Icc 1 6 ∧ ∀ a b : ℤ, 3 * b = 8 - 2 * a → x ∣ 2 * b + 12}.ncard = 3 := by
  -- It suffices to prove that the set is {1, 2, 4}
  suffices H : {x : ℤ | x ∈ Finset.Icc 1 6 ∧ ∀ a b : ℤ, 3 * b = 8 - 2 * a → x ∣ 2 * b + 12} = {1, 2, 4} by
    rw [H]
    simp
  -- We have two goals to prove:
  -- 1. If x is in the set, then x = 1, 2, or 4
  -- 2. If x = 1, 2, or 4, then x is in the set
  ext x
  constructor
  . -- First goal
    rintro ⟨hx, h⟩
    -- We set a = 1 and b = 2 in h
    specialize h 1 2
    -- And we get x ∣ 16
    simp at h hx ⊢
    rcases hx with ⟨h1, h2⟩
    -- x ∈ [1, 6], so x = 1, 2, 3, 4, 5, or 6
    interval_cases x
    -- All the subgoals are trivial:
    -- Either the goal is trivially true (x = 1, 2, or 4)
    -- Or h is false (x = 3, 5, or 6)
    all_goals
      trivial
  . -- Second goal
    intro h
    simp
    -- If x = 1, 2, or 4, we need to prove that x is in the set
    constructor
    . -- First, x ∈ [1, 6]
      -- Just do case analysis on x = 1, 2, or 4
      rcases h with rfl | rfl | rfl
      all_goals
        simp
    . intro a b H
      -- To prove that x ∣ 2b + 12 for any x ∈ {1, 2, 4}
      -- It suffices to prove that 4 ∣ 2b + 12
      suffices G : 4 ∣ 2 * b + 12 by
        -- Case analysis on x = 1, 2, or 4
        rcases h with rfl | rfl | rfl
        . simp
        . -- If 4 ∣ 2b + 12, then 2 ∣ 2b + 12
          rcases G with ⟨k, hk⟩
          use 2 * k
          simp [hk]
          ring
        . exact G
      clear x h
      -- Now we focus on proving 4 ∣ 2b + 12
      -- We have 3b = 8 - 2a is even
      have h : Even (3 * b) := ⟨4 - a, by linarith⟩
      -- 3 is odd, so b is even
      rw [Int.even_mul] at h
      -- Note that the use of decide can be replaced by hand computation
      simp [show ¬ Even (3 : ℤ) by decide] at h
      -- So b = 2k for some k
      rcases h with ⟨k, rfl⟩
      -- And 2b + 12 = 4k + 12 = 4(k + 3)
      use k + 3
      ring
