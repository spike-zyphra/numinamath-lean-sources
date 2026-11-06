import Mathlib

open Real

set_option maxHeartbeats 0

/- 9. The three prime numbers $a, b, c$ satisfy $a < b < c < 100$, and $(b-a) \times(c-b) \times(c-a)=240$, then the maximum sum of the three prime numbers $a, b, c$ is $\qquad$ _. -/
theorem number_theory_153614 (a b c : ℕ)
  (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
  (hord : a < b ∧ b < c ∧ c < 100)
  (hprod : (b - a) * (c - b) * (c - a) = 240) :
  a + b + c ≤ 251 := by
  -- Show each prime is at most 97, since they lie below 100
  have h₁ : a ≤ 97 := by
    have h₁₁ : a < 100 := by linarith
    -- Do a finite case‐split on a ∈ finset.range 100
    interval_cases a
    -- Discharge non‐prime options
    <;> norm_num [Nat.Prime] at ha ⊢

  have h₂ : b ≤ 97 := by
    -- Similarly bound b < 100
    have h₂₁ : b < 100 := by linarith
    interval_cases b
    <;> norm_num [Nat.Prime] at hb ⊢

  have h₃ : c ≤ 97 := by
    -- Similarly bound c < 100
    have h₃₁ : c < 100 := by linarith
    interval_cases c
    <;> norm_num [Nat.Prime] at hc ⊢

  -- Now perform the main case analysis on a
  interval_cases a
  -- Discharge non‐prime values
  <;> norm_num [Nat.Prime] at ha ⊢
  -- Attempt to finish each goal with omega, or go further if fails
  <;>
    (try omega) <;>
    -- If omega alone doesn’t close the goal, split b
    (try
      {
        interval_cases b
        -- Discharge non‐prime values and use the product‐eq hypothesis
        <;> norm_num [Nat.Prime] at hb hprod ⊢ <;>
          -- again try omega
          (try omega) <;>
          -- If needed, split c
          (try
            {
              interval_cases c
              -- Discharge non‐prime values and use hprod
              <;> norm_num [Nat.Prime] at hc hprod ⊢
            })
      })