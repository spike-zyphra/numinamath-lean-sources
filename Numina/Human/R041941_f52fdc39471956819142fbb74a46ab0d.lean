import Mathlib



/- The first term of a given sequence is 1, and each successive term is the sum of all the previous terms of the sequence. What is the value of the first term which exceeds 5000? -/
theorem algebra_10335
    (a : ℕ → ℕ)
    (ha0 : a 0 = 1)
    (han : ∀ n, a (n + 1) = ∑ i ∈ Finset.Icc 0 n, a i) :
    IsLeast {vn | ∃ n, a n > 5000 ∧ a n = vn} 8192 := by

  -- aux lemma
  have l_lt {a b : ℕ} : a < b → 2 ^ a < 2 ^ b := by
    intro h
    set d := b - a
    rw [show b = a + d by omega, pow_add]
    apply (Nat.lt_mul_iff_one_lt_right ?_).mpr ?_
    . exact Nat.two_pow_pos a
    . apply Nat.one_lt_two_pow_iff.mpr
      omega

  -- aux lemma
  have l_le {a b : ℕ} : a ≤ b → 2 ^ a ≤ 2 ^ b := by
    intro h
    set d := b - a
    rw [show b = a + d by omega, pow_add]
    apply Nat.le_mul_of_pos_right
    exact Nat.two_pow_pos d

  -- Let's prove by induction that the $n$th term of the sequence is $2^{n-2}$ for all integers $n\geq 2$.
  have ra : ∀ d, a (d + 1) = 2 ^ d := by
    intro d
    induction' d using Nat.strong_induction_on with d ih
    cases d

    ---- The base case $n=2$ holds since the second term of the sequence is the sum of all the terms before it, which is just 1.
    case zero => simp [han, ha0]
    -- For the induction step, let $n>2$ and suppose that the $(n-1)$st term is $2^{n-1-2}=2^{n-3}$.
    case succ d =>
      -- Then the sum of the first $n-2$ terms of the sequence is $2^{n-3}$
      have : ∑ i ∈ Finset.Icc 0 (d + 1), a i = 2 ^ (d + 1) := by
        induction d with
        | zero =>
          calc
            _ = a 0 + a 1 := by rfl
            _ = 2 := by simp [han, ha0]
        | succ d' ih' =>
          calc
            _ = ∑ i ∈ Finset.Icc 0 (d' + 1), a i + a (d' + 1 + 1) := by
              rw [show Finset.Icc 0 (d' + 1 + 1) = Finset.Ico 0 (d' + 1 + 1 + 1) by rfl,
                  show Finset.Icc 0 (d' + 1) = Finset.Ico 0 (d' + 1 + 1) by rfl,
                  Nat.Ico_zero_eq_range, Finset.sum_range_succ]
            _ = 2 ^ (d' + 1 + 1) := by
              rw [ih' _, ih, ← two_mul, ← pow_succ']
              . exact lt_add_one (d' + 1)
              . intro x hx
                exact ih x (by linarith only [hx])
      rw [han, this]

  -- Since $2^{12}=4096$, the first power of 2 that exceeds 5000 is $2^{13}=\boxed{8192}$.
  constructor
  . dsimp
    use 14
    simp [ra]
  . simp [lowerBounds]
    intro n hn
    rw [show 8192 = 2 ^ 13 by norm_num]
    rcases Nat.lt_or_ge n 14 with h | h
    . rcases Nat.eq_zero_or_pos n with heq0 | hne0
      . rw [heq0, ha0] at hn
        contradiction
      . rcases eq_or_ne n 13 with heq13 | hne13
        . simp [heq13, ra] at hn
        . specialize ra (n - 1)
          rw [Nat.sub_add_cancel hne0] at ra
          have : (n - 1) < 12 := by omega
          specialize l_lt this
          simp [← ra] at l_lt
          linarith
    . rcases eq_or_ne n 14 with heq14 | _
      . simp [heq14, ra]
      . have : 13 ≤ n - 1 := by omega
        convert l_le this using 1
        convert ra (n - 1)
        omega
