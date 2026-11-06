import Mathlib

/-
Let $N=\overline{5AB37C2}$, where $A, B, C$ are digits between 0 and 9,
inclusive, and $N$ is a 7-digit positive integer.
If $N$ is divisible by 792, determine all possible ordered triples $(A, B, C)$.
-/
theorem number_theory_608925 (a b c : ℤ) (ha : 0 ≤ a ∧ a ≤ 9) (hb : 0 ≤ b ∧ b ≤ 9) (hc : 0 ≤ c ∧ c ≤ 9)
  : (792 ∣ 5*10^6 + a*10^5 + b*10^4 + 3700 + c*10 + 2 ) ↔ (a, b, c) ∈ [(0, 5, 5), (4, 5, 1), (6, 4, 9)] := by

  simp
  constructor
  . intro h
    -- Claim 1: c = 1 or c = 5 or c = 9
    -- This is obtained as follows:
    -- Since 8 is a factor of 792 and 10^3, 10^4, 10^5, and 10^6 are divisible by 8,
    -- 792 ∣ 5 * 10^6 + a * 10^5 + b * 10^4 + 3700 + c * 10 + 2
    -- implies that 8 ∣ 10c + 6, implying c = 1 or c = 5 or c = 9.
    have claim1 : c = 1 ∨ c = 5 ∨ c = 9 := by revert a; revert b; revert c; simp; decide

    -- Claim 2: a + b + c = 1 or a + b + c = 10 or a + b + c = 19
    -- This is obtained as follows:
    -- Since 9 is a factor of 792,
    -- 792 ∣ 5 * 10^6 + a * 10^5 + b * 10^4 + 3700 + c * 10 + 2
    -- implies that 9 ∣ 5 * 10^6 + a * 10^5 + b * 10^4 + 3700 + c * 10 + 2,
    -- which implies that 9 ∣ 5 + a + b + 3 + 7 + c + 2,
    -- which implies that 9 ∣ a + b + c - 1,
    -- which implies that a + b + c = 1 or a + b + c = 10 or a + b + c = 19.
    have claim2 : a + b + c = 1 ∨ a + b + c = 10 ∨ a + b + c = 19 := by revert a; revert b; revert c; simp; decide

    -- Claim 3: -a + b - c = -11 or -a + b - c = 0
    -- This is obtained as follows:
    -- Since 11 is a factor of 792,
    -- 792 ∣ 5 * 10^6 + a * 10^5 + b * 10^4 + 3700 + c * 10 + 2
    -- implies that 11 ∣ 5 * 10^6 + a * 10^5 + b * 10^4 + 3700 + c * 10 + 2,
    -- which implies that 11 ∣ 5 - a + b - 3 + 7 - c + 2
    -- which implies that 11 ∣ -a + b - c,
    -- which implies that - a + b + c = -11 or - a + b + c = 0.
    have claim3 : -a + b - c = -11 ∨ -a + b - c = 0 := by revert a; revert b; revert c; simp; decide

    -- Claim 4: b = 4 or b = 5
    -- To see this, note that 2 * b = (a + b + c) + (- a + b + c) is even.
    -- From from Claim 2 and Claim 3, we obtain that b = 4 or b = 5.
    have claim4 : b = 4 ∨ b = 5 := by revert a; revert b; revert c; simp; decide

    revert h

    -- Use Claim 4 to split into two cases.
    rcases claim4 with g | g
    . -- Consider the case when b = 4

      -- Use Claim 1 to split into three cases.
      rcases claim1 with hc' | hc' | hc'

      -- Substitute the values of b and c into the statements of Claim 2 and Claim 3 and the goal.
      -- Simplifying proves the result.
      all_goals rw [g, hc'] at claim2 claim3 ⊢
      repeat
        revert b; revert c; revert a
        simp
        decide
    . -- Consider the case when b = 5
      rcases claim1 with hc' | hc' | hc'

      -- Substitute the values of b and c into the statements of Claim 2 and Claim 3 and the goal.
      all_goals rw [g, hc'] at claim2 claim3 ⊢; ring_nf at *; simp at *
      . -- Use Claim 3 to split into two cases.
        rcases claim3 with ha' | ha'
        . -- The case when 4 - a = -11.
          -- Simplifying gives a = 15.
          -- Substituting this value for a in 792 ∣ 5053712 + a * 100000 gives False.
          obtain hav : a = 15 := by linarith
          rw [hav]; decide
        . -- The case when 4 - a = 0.
          -- Simplifying gives a = 4.
          -- Substituting this value for a in 792 ∣ 5053712 + a * 100000 gives False.
          obtain hav : a = 4 := by linarith
          rw [hav]; decide
      . -- Use Claim 3 to split into two cases.
        rcases claim3 with ha' | ha'
        -- In both cases, substituting this value for a in 792 ∣ 5053712 + a * 100000 gives False.
        repeat rw [ha']; decide
      . -- Use Claim 3 to split into two cases.
        rcases claim3 with ha' | ha'
        . -- The case when -4 - a = -11.
          -- Simplifying gives a = 7.
          -- Substituting this value for a in 792 ∣ 5053712 + a * 100000 gives False.
          obtain hav : a = 7 := by linarith
          rw [hav]; decide
        . -- The case when -4 - a = 0.
          -- Simplifying gives a = -4.
          -- Substituting this value for a in 792 ∣ 5053712 + a * 100000 gives False.
          obtain hav : a = -4 := by linarith
          rw [hav] at ha
          norm_num at ha
  . intro h
    -- Consider each case of a = 0 ∧ b = 5 ∧ c = 5, a = 4 ∧ b = 5 ∧ c = 1, a = 6 ∧ b = 4 ∧ c = 9 in turn
    rcases h with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
    -- Each case is shown to be true by direct calculations.
    repeat rw [a, b, c]; decide
  done
