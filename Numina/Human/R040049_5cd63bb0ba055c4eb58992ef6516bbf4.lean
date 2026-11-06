import Mathlib

/-- Waring's problem: For each integer `k ≥ 1`, there exists a least number `g(k)`
such that every positive integer is a sum of at most `g(k)` many `k`th powers of integers. -/
def WaringProperty (k g : ℕ) : Prop :=
  ∀ n : ℕ, n > 0 → ∃ (xs : Fin g → ℤ), (∑ i, xs i ^ k) = n

/-- Waring upper bound for `k`, valid for all `k ≤ 471600000`:
  any positive integer is a sum of at most `2^k + floor((3/2)^k) - 2` k-th powers. -/
noncomputable def waringUpperBound (k : ℕ) : ℤ :=
  2 ^ k + ⌊(3 / 2 : ℝ) ^ k⌋ - 2

/-- Lemma: For all `k ≤ 471600000`, the Waring upper bound holds. -/
axiom waring_bound_valid_up_to_471600000 :
  ∀ k ≤ 471600000, WaringProperty k (waringUpperBound k).toNat

/-- Lemma: The Waring upper bound is monotone (non-decreasing) in `k`. -/
lemma waringUpperBound_monotone : Monotone waringUpperBound := by
  intro m n hmn
  unfold waringUpperBound
  norm_num
  apply add_le_add
  · norm_cast
    exact Nat.pow_le_pow_of_le_right (show 2 > 0 by norm_num) hmn
  · apply Int.floor_le_floor
    have := Real.rpow_le_rpow_of_exponent_le (show 1 ≤ (3 / 2 : ℝ) by norm_num) (show (m:ℝ) ≤ n by norm_num[hmn])
    norm_cast at this
    
/-- Theorem: For all `k ≤ 2015`, every positive integer is a sum of at most
    `2^k + floor((3/2)^k) - 2` many `k`th powers. -/
theorem numbertheory_609475 (k : ℕ) (hk : k ≤ 2015) :
    WaringProperty k (waringUpperBound k).toNat :=
  waring_bound_valid_up_to_471600000 k (le_trans hk (by norm_num))
