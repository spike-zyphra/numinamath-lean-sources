import Mathlib

/-
The increasing sequence 3,15,24,48,… consists of those positive multiples of 3 that are one less
than a perfect square. What is the remainder when the 1994th term of the sequence is divided by
1000?
-/

-- A naive representation of the sequence could be :
-- noncomputable def seq : ℕ → ℕ
--   | 0 => sInf { m | m % 3 = 0 ∧ ∃ n, m = n^2 - 1 }
--   | k + 1 => sInf { m > seq k | m % 3 = 0 ∧ ∃ n, m = n^2 - 1 }

-- However notice the following fact : given a positive integer n, (n^2 - 1) % 3 = 0  iff  (n % 3 = 1 or n % 3 = 2)
theorem fact (n : ℕ) (hn : n ≠ 0) : (n^2 - 1) % 3 = 0 ↔ (n % 3 = 1 ∨ n % 3 = 2) := by
  -- Reasoning about mod is more convenient in ℤ
  by_cases h1 : n^2 ≥ 1
  case neg =>
    have h1 : n^2 = 0 := by exact Nat.eq_zero_of_not_pos h1
    have h1 : n = 0 := by exact pow_eq_zero h1
    contradiction
  zify [h1]
  constructor
  . intro h1
    have h2 : (n % 3 = 0 ∨ n % 3 = 1) ∨ n % 3 = 2 := by
      have h1 : n % 3 < 3 := by
        apply Nat.mod_lt
        norm_num
      have h1 : n % 3 ≤ 2 := by exact Nat.le_of_lt_succ h1
      have h1 : (n % 3 ≤ 0 ∨ n % 3 = 1) ∨ n % 3 = 2 := by
        iterate 2 rw [Nat.le_succ_iff] at h1
        exact h1
      have h2 : n % 3 ≤ 0 ↔ n % 3 = 0 := by exact Nat.le_zero
      rw [h2] at h1
      exact h1
    rcases h2 with (h2 | h2) | h2
    -- If n % 3 = 0
    . zify at h2
      -- Show a contradiction
      have h3 : (n : ℤ)^2 = n * n  := by ring
      rw [h3, Int.sub_emod, Int.mul_emod, h2] at h1
      norm_num at h1
    -- If n % 3 = 1
    . zify at h2
      simp [h2]
    -- If n % 3 = 2
    . zify at h2
      simp [h2]
  . intro h1
    rcases h1 with h1 | h1
    all_goals
      have h2 : (n : ℤ)^2 = n * n  := by ring
      rw [h2, Int.sub_emod, Int.mul_emod, h1]
      norm_num

-- A convenient representation of the sequence is therefore :
def u (k : ℕ) : ℕ :=
  -- n is the k-th natural integer obtained by skipping every multiple of 3
  let n := (k / 2) * 3 + k % 2 + 1
  n^2 - 1

theorem number_theory_705 : u 1994 % 1000 = 63 := by
  -- Expand u
  rw [u]
  -- Computing both sides is straightforward
  norm_num