import Mathlib
open Nat Finset

/-
Estimate $A$, the number of times an 8-digit number appears in Pascal's triangle. An estimate of $E$ earns $\max (0,\lfloor 20-|A-E| / 200\rfloor)$ points.
-/

-- Step 1: Occurrences from choose N 1 and choose N (N-1) (A_trivial)
-- Number of 8-digit numbers: (10^8 - 1) - 10^7 + 1 = 9 * 10^7
def num_8_digit_numbers : ℕ := (10^8 - 1) - 10^7 + 1

lemma num_8_digit_numbers_val : num_8_digit_numbers = 90000000 := by
  unfold num_8_digit_numbers
  norm_num

def A_trivial : ℕ := 2 * num_8_digit_numbers

lemma A_trivial_val : A_trivial = 180000000 := by
  unfold A_trivial num_8_digit_numbers
  norm_num

-- Step 2: Occurrences from choose n k for 2 ≤ k ≤ n-2 (A_other)
-- We count pairs (n,k) with 2 ≤ k ≤ n/2.
-- If k < n/2 (n > 2k), it contributes 2 occurrences.
-- If k = n/2 (n = 2k), it contributes 1 occurrence (central coefficient).

-- Pre-calculated (n_min, n_max) bounds for each k where choose n k is an 8-digit number
-- and n ≥ 2k. These values are derived from the detailed analysis in the problem description.
def n_bounds_for_k_val (k : ℕ) : (ℕ × ℕ) :=
  match k with
  | 2  => (4473, 14142)
  | 3  => (393, 844)
  | 4  => (126, 222)
  | 5  => (68, 105)
  | 6  => (47, 67)
  | 7  => (38, 55)
  | 8  => (32, 49)
  | 9  => (29, 42)
  | 10 => (28, 40)
  | 11 => (27, 37)
  | 12 => (26, 32)
  | 13 => (26, 35) -- n_min = 2k for k=13 (choose 26 13)
  | 14 => (28, 34) -- n_min = 2k for k=14 (choose 28 14)
  | _  => (0, 0)   -- No 8-digit numbers for other k (or k < 2 or k > 14)

-- Contribution to A_other for a given k, using its pre-calculated n_min and n_max.
def A_other_term_for_k (k : ℕ) : ℕ :=
  let bounds := n_bounds_for_k_val k
  let n_min := bounds.1
  let n_max := bounds.2
  if h_valid_range : n_min > 0 ∧ n_min ≤ n_max then -- Ensure the range is valid and non-empty
    let num_n_values := n_max - n_min + 1
    if n_min = 2 * k then -- Central coefficient is the first in range (e.g., k=13, n_min=26)
      if num_n_values = 0 then 0 -- Should not happen if n_min <= n_max
      else if num_n_values = 1 then 1 -- Only the central coefficient
      else 1 + 2 * (num_n_values - 1) -- 1 for central, 2 for each of the non-central
    else -- All values in range are non-central (n > 2k because n_min > 2k)
      2 * num_n_values
  else 0 -- No valid n range for this k

-- Calculate A_other by summing these terms
def A_other_computed : ℕ :=
  Finset.sum (Finset.Icc 2 14) (fun k => A_other_term_for_k k)

lemma A_other_computed_val : A_other_computed = 20750 := by
  unfold A_other_computed A_other_term_for_k
  native_decide
  

-- Step 3: Total Estimated Occurrences E
def E_estimate : ℕ := A_trivial + A_other_computed

theorem combinatorics_610237 : E_estimate = 180020750 := by
  unfold E_estimate
  rw [A_trivial_val, A_other_computed_val]


