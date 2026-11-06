import Mathlib

/- For each positive integer $n$, let $S(n)$ denote the sum of the digits of $n.$ For how many values of $n$ is $n + S(n) + S(S(n)) = 2007?$
$\mathrm{(A)}\ 1 \qquad \mathrm{(B)}\ 2 \qquad \mathrm{(C)}\ 3 \qquad \mathrm{(D)}\ 4 \qquad \mathrm{(E)}\ 5$ -/
theorem number_theory_96759 :
    let S : ℕ → ℕ := fun n ↦ (Nat.digits 10 n).sum
    {n | n > 0 ∧ n + S n + S (S n) = 2007}.ncard = 4 := by
  intro S
  have hS : S = fun n ↦ (Nat.digits 10 n).sum := rfl

  -- We prove the statement by establishing the set of n directly.
  suffices hn : {n | n > 0 ∧ n + S n + S (S n) = 2007} = {1977, 1980, 1983, 2001} by
    simp [hn, Set.ncard, Set.encard]

  ext n
  simp_rw [Set.mem_setOf]
  use ?_, fun hn ↦ by simp at hn; rcases hn with rfl | rfl | rfl | rfl <;> simp [hS]
  intro ⟨hn_pos, hn⟩
  rw [add_assoc] at hn

  -- We begin by proving a trivial bound: n ≤ 2007 as S(n) and S(S(n)) are nonnegative.
  have hn_le : n ≤ 2007 := hn ▸ Nat.le_add_right n (S n + S (S n))

  -- Next, we prove an auxiliary lemma: the sum of a list consisting of natural numbers can be upper
  -- bounded by the maximum element and the length.
  have sum_le_length_mul (l : List ℕ) (b : ℕ) (hl : ∀ d ∈ l, d ≤ b) :
      l.sum ≤ l.length * b := by
    induction' l with x xs ih
    · simp
    · specialize ih fun d hd ↦ hl d (List.mem_cons_of_mem x hd)
      simp [add_mul, add_comm]
      gcongr
      exact hl x (List.mem_cons_self x xs)

  -- This yields an upper bound for S(n).
  have hS_le (a k : ℕ) (ha_ne : a ≠ 0) (ha_le : a ≤ 10 ^ k) : S a ≤ 9 * (k + 1) := by
    have := Nat.base_pow_length_digits_le 10 a (by decide) ha_ne
    have := this.trans (show 10 * a ≤ 10 ^ (k + 1) by
      rw [pow_add, pow_one, mul_comm]
      gcongr
    )
    have hl : (Nat.digits 10 a).length ≤ k + 1 := (Nat.pow_le_pow_iff_right (by decide)).mp this
    have ha (d : ℕ) (hd : d ∈ Nat.digits 10 a) : d < 10 := Nat.digits_lt_base (by decide) hd
    have ha' (d : ℕ) (hd : d ∈ Nat.digits 10 a) : d ≤ 9 := Nat.le_of_lt_succ (ha d hd)

    refine (sum_le_length_mul _ _ ha').trans ?_
    linarith

  -- Also, we get a lower bound for the sum of a list by one of its elements.
  have getLast_le_sum {l : List ℕ} {hl : l ≠ []} : l.getLast hl ≤ l.sum := by
    induction' l with x xs ih
    · simp at hl
    · by_cases hxs : xs = []
      · subst hxs
        simp
      · simp [List.getLast_cons hxs]
        exact ih.trans <| Nat.le_add_left xs.sum x

  -- In particular, this shows that S(n) is nonzero.
  have hS_ne_zero (a : ℕ) (ha : a ≠ 0) : S a ≠ 0 := by
    have := Nat.getLast_digit_ne_zero 10 ha
    have : (Nat.digits 10 a).getLast (Nat.digits_ne_nil_iff_ne_zero.mpr ha) ≤ S a := getLast_le_sum
    omega

  -- This yields a lower bound for n, as S(n) + S(S(n)) is upper bounded.
  have hS₁ : S n ≤ 45 := hS_le _ _ hn_pos.ne.symm (show n ≤ 10 ^ 4 by linarith)
  have hS₂ : S (S n) ≤ 27 := hS_le _ _ (hS_ne_zero _ hn_pos.ne.symm) (show S n ≤ 10 ^ 2 by linarith)
  have hn_ge : 1935 ≤ n := by linarith

  -- Finally, we check the finite number of candidates.
  revert hn
  apply Iff.mp
  interval_cases n <;> native_decide