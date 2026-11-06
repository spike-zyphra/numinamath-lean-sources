import Mathlib

open Nat

/- Example 39 (2004 Croatian Mathematical Competition Problem) Prove: the sum of the squares of any five consecutive positive integers is not a perfect square of a positive integer.

Keep the original text's line breaks and format, and output the translation result directly. -/
theorem number_theory_114877 (n : ℕ) (h₀ : n > 0) :
    ¬ ∃ m, m^2 = ∑ i ∈ Finset.range 5, (n + i)^2 := by
  rintro ⟨m, hm⟩
  repeat rw [Finset.sum_range_succ] at hm
  simp at hm
  -- Rewrite the sum as 5 * ((n + 2) ^ 2 + 2)
  have m_sq : m ^ 2 = 5 * ((n + 2) ^ 2 + 2) := by rw [hm]; ring
  -- Show that 5 must divide (n + 2) ^ 2 + 2
  have five_dvd : 5 ∣ (n + 2) ^ 2 + 2 := by
    -- Use contradiction
    by_contra not_dvd
    -- Show that (n + 2) ^ 2 + 2 has no 5s in its factorization
    have : Nat.factorization ((n + 2) ^ 2 + 2) 5 = 0 := factorization_eq_zero_of_not_dvd not_dvd
    -- The RHS of m_sq has one 5 in its factorization
    have : Nat.factorization (5 * ((n + 2) ^ 2 + 2)) 5 = 1 := by rw [factorization_mul (by positivity) (by positivity)]; norm_num; tauto
    -- The LHS of m_sq is even
    have : Nat.factorization (m ^ 2) 5 = 2 * Nat.factorization m 5 := by simp
    -- Apply factorization to both sides of m_sq
    apply_fun (fun n => Nat.factorization n 5) at m_sq
    -- Since the LHS is even while the RHS is 1, we have a contradiction
    omega
  -- Show that 3 is not a quadratic residue mod 5 by manually checking every residue
  have three_not_qr : ∀ m, m ^ 2 % 5 ≠ 3 := by
    intro m
    have : m % 5 < 5 := mod_lt m (by positivity)
    have : m ^ 2 % 5 = (m % 5) ^ 2 % 5 := by simp [pow_mod]
    interval_cases m % 5
    all_goals
      simp at this
      linarith
  rw [dvd_iff_mod_eq_zero] at five_dvd
  specialize three_not_qr (n + 2)
  rw [add_mod] at five_dvd
  -- (n + 2) ^ 2 must leave a remainder of 3 mod 5
  have : (n + 2) ^ 2 % 5 = 3 := by omega
  -- This contradicts three_not_qr
  tauto