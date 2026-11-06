import Mathlib

/-
Prove the difference in probabilities for reaching specific numbers in a random walk. Starting from 0, Casey randomly adds 1 or 2 (each with probability 1/2) to the current number. Let pₘ be the probability that Casey ever reaches the number m. We aim to show that p₂₀ - p₁₅ = 11/2²⁰.
-/
theorem Combinatorics_609366
    {p : ℕ → ℝ}
    (hp0 : p 0 = 1)
    (hpn : ∀ n, p n = 1 - 1 / 2 * p (n - 1)) :
    p 20 - p 15 = (11 : ℝ)/(2 ^ 20 : ℝ) := by

  -- First, show that the recurrence relation for p(n) can be transformed into a geometric sequence form
  have h_geom : ∀ n, n > 0 → p n - 2 / 3 = -1 / 2 * (p (n - 1) - 2 / 3) := by
    intro n hn
    rw [hpn n]
    ring

  -- Next, use induction to prove the closed-form expression for p(n)
  have pn_closed_form : ∀ n, p n = 2 / 3 + (1 / 3) * (-1 / 2) ^ n := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero]
      calc
        p 0 = 1 := by rw [hp0]
        _ = 2 / 3 + 1 / 3 := by norm_num
        _ = 2 / 3 + (1 / 3) * 1 := by rw [mul_one]
    | succ k ih =>
      rw [hpn (k + 1)]
      simp [ih]
      ring

  -- Finally, substitute n=20 and n=15, compute the difference and simplify
  rw [pn_closed_form 20, pn_closed_form 15]
  ring_nf
  
