import Mathlib

open Finset Real

/- 18th USAMO 1989 Problem 1 Let a n = 1 + 1/2 + 1/3 + ... + 1/n, b n = a 1 + a 2 + ... + a n , c n = b 1 /2 + b 2 /2 + ... + b n /(n+1). Find b 1988 and c 1988 in terms of a 1989 . -/
theorem algebra_122683 {a b c : ℕ → ℝ}
    (ha : ∀ n, a n = ∑ i ∈ Icc 1 n, (1 : ℝ)/i)
    (hb : ∀ n, b n = ∑ i ∈ Icc 1 n, a i)
    (hc : ∀ n, c n = ∑ i ∈ Icc 1 n, (b i)/(i+1)) :
    b 1988 = 1989 * a 1989 - 1989 ∧ c 1988 = 1990 * a 1989 - 3978 := by
  -- We have obvious identities:
  -- a (n + 1) = a n + 1 / (n + 1),
  -- b (n + 1) = b n + a (n + 1),
  -- c (n + 1) = c n + b (n + 1) / (n + 2).
  have ha1 n : a (n + 1) = a n + 1 / (n + 1) := by simp [ha, sum_Icc_succ_top]
  have hb1 n : b (n + 1) = b n + a (n + 1) := by simp [hb, sum_Icc_succ_top]
  have hc1 n : c (n + 1) = c n + b (n + 1) / (n + 2) := by
    simp [hc, sum_Icc_succ_top, show (n : ℝ) + 1 + 1 = n + 2 by ring]
  -- Prove that b n = (n + 1) * (a (n + 1) - 1).
  have hba n : b n = (n + 1) * (a (n + 1) - 1) := by
    -- Proof by induction
    induction n with
    -- n = 0 is obvious.
    | zero => simp [hb, ha]
    | succ n ih =>
      -- Assume that b n = (n + 1) * (a (n + 1) - 1) and show that
      -- b (n + 1) = (n + 2) * (a (n + 2) - 1).
      -- We have b (n + 1) = b n + a (n + 1) = (n + 1) * (a (n + 1) - 1) + a (n + 1).
      -- On the other hand, we have (n + 2) * (a (n + 2) - 1)
      --     = (n + 2) * (a (n + 1) + 1 / (n + 2) - 1) = (n + 2) * a(n + 1) + 1 - n - 2.
      -- It is easy to see that both sides are equal.
      rw [hb1, ih, ha1 (n + 1)]
      field_simp
      ring
  -- We can write b(1988) = 1989 * (a(1989) - 1).
  rw [hba 1988]
  refine ⟨by ring, ?_⟩
  -- Prove that c n = (n + 2) * a (n + 1) - 2 * (n + 1).
  have hca n : c n = (n + 2) * a (n + 1) - 2 * (n + 1) := by
    -- Proof by induction.
    induction n with
    -- n = 0 is obvious.
    | zero => simp [hc, hb, ha]
    | succ n ih =>
      -- Assume that c n = (n + 2) * a (n + 1) - 2 * (n + 1) and show that
      -- c (n + 1) = (n + 3) * a (n + 2) - 2 * (n + 2).
      -- We have c (n + 1) = c (n) + b (n + 1) / (n + 2) = c (n) + (n + 2) * (a (n + 2) - 1).
      -- We also have a(n + 2) = a(n + 1) + 1 / (n + 2).
      -- The result follows from algebraic simplifications.
      rw [hc1, ih, hba, ha1 (n + 1)]
      field_simp
      ring
  -- We can write c(1988) = 1990 * a(1989) - 2 * 1989.
  rw [hca]
  ring