import Mathlib

/- Find the remainder when $1 + 2 + 2^2 + 2^3 + \dots + 2^{100}$ is divided by 7. -/
theorem number_theory_23059 : (∑ i ∈ Finset.range 101, 2^i) % 7 = 3 := by
  -- Prove the sum of the first 101 powers of 2 is 2^101 - 1
  -- Generalize it from 101 to n
  have H n : ∑ i in Finset.range n, 2^i = 2^n - 1 := by
    -- Prove by induction
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      omega
  -- Apply the above result
  rw [H]
  clear H
  -- 2^101 = (2^3)^33 * 2^2
  calc (2 ^ 101 - 1) % 7
       _ = (2 ^ (3 * 33 + 2) - 1) % 7 := by rw [show 101 = 3 * 33 + 2 by norm_num]
       _ = ((2 ^ 3) ^ 33 * 2 ^ 2 - 1) % 7 := by rw [pow_add, pow_mul]
       _ = 3 := ?_
  change (2 ^ 3) ^ 33 * 2 ^ 2 - 1 ≡ 3 [MOD 7]
  rw [Nat.modEq_iff_dvd]
  -- It suffices to prove 7 divides -4 * (8 ^ 33 - 1)
  have H : ((3 : ℕ) - (((2 ^ 3) ^ 33 * 2 ^ 2 - 1) : ℕ) : ℤ) = -4 * (8 ^ 33 - 1) := by simp
  rw [H]
  clear H
  -- It suffices to prove 7 divides 8 ^ 33 - 1
  suffices K : (7 : ℤ) ∣ 8 ^ 33 - 1 by
    have ⟨n, hn⟩ := K
    use -4 * n
    rw [hn]
    ring
  -- Which follows from the lemma:
  -- x - 1 divides x^n - 1
  apply sub_one_dvd_pow_sub_one
