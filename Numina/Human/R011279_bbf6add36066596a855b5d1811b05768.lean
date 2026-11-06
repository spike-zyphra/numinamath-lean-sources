import Mathlib

open Finset

/- 11.1. Given the sequence $a_{n}=(-1)^{1+2+\ldots+n}$. Find $a_{1}+a_{2}+\ldots+a_{2017}$. -/
theorem algebra_232778 (a : ℕ → ℤ) (ha : ∀ n, a n = (-1) ^ (∑ i ∈ Icc 1 n, i)) :
    ∑ i ∈ Icc 1 2017, a i = -1 := by
  -- a is periodic with period 4
  -- With a₀ = 1, a₁ = -1, a₂ = -1, a₃ = 1
  have H₁ (n : ℕ) :
      a n = match n % 4 with
            | 0 => 1
            | 1 => -1
            | 2 => -1
            | 3 => 1
            | _ => 0 := by
    -- We proceed by induction on n
    induction n with
    | zero => simp [ha] -- Base case is trivial
    | succ n ih =>
      -- Inductive step
      simp [ha] at ih ⊢
      -- Rewrite the sum of the first n+1 integers as a sum of the first n integers plus n+1, then use the inductive hypothesis
      rw [Finset.sum_Icc_succ_top (by simp), pow_add, ih]
      -- Casework on the remainder when n is divided by 4
      mod_cases hn : n % 4
      all_goals
        simp [Nat.ModEq] at hn
        -- Now n % 4 and (n + 1) % 4 can be computed, now we can simplify and eliminate the `match` expression
        simp [Nat.add_mod, hn, pow_succ]
        -- We compute n % 2
        have hn₂ : n % 2 = (n % 4) % 2 := (Nat.mod_mod_of_dvd n (by decide)).symm
        simp [hn] at hn₂
        first |
          -- If n % 2 = 0, then n is even
          rw [← Nat.even_iff] at hn₂
          simp [Even.neg_one_pow hn₂] |
          -- If n % 2 = 1, then n is odd
          rw [← Nat.odd_iff] at hn₂
          simp [Odd.neg_one_pow hn₂]
  -- a is periodic with period 4
  have H₂ (n : ℕ) : a (n + 4) = a n := by
    simp [H₁]
  -- The sum of 4 consecutive terms of a is 0 by simple induction
  have H₃ (n : ℕ) : a n + a (n + 1) + a (n + 2) + a (n + 3) = 0 := by
    induction n with
    | zero => simp [H₁]
    | succ n ih =>
      rw [H₂]
      linarith only [ih]
  -- So S_{n + 4} = S_n
  have H₄ (n : ℕ) : ∑ i ∈ Icc 1 (n + 4), a i = ∑ i ∈ Icc 1 n, a i := by
    rw [Finset.sum_Icc_succ_top (by simp), Finset.sum_Icc_succ_top (by simp), Finset.sum_Icc_succ_top (by simp), Finset.sum_Icc_succ_top (by simp)]
    linear_combination H₃ (n + 1)
  -- Therefore, S_{n + 4k} = S_n by simple induction
  have H₅ (n k : ℕ) : ∑ i ∈ Icc 1 (n + 4 * k), a i = ∑ i ∈ Icc 1 n, a i := by
    induction k with
    | zero => simp
    | succ k ih => rwa [Nat.mul_succ, ← Nat.add_assoc, H₄]
  -- So we have S_{2017} = S_{1} = -1
  simpa [show a 1 = -1 by simp [H₁]] using H₅ 1 504
