import Mathlib

/-For each positive integer $k$, let $S_k$ denote the increasing arithmetic sequence of integers whose first term is 1 and whose common difference is $k$.  For example, $S_3$ is the sequence $1,4,7,\ldots$.  For how many values of $k$ does $S_k$ contain $2005$ as a term?-/
theorem algebra_19696 (S : ℕ → Set ℕ) (hS : ∀k, S k = {x | ∃ n, x = 1 + k * n}):
    Set.ncard {k | 0 < k ∧ 2005 ∈ S k} = 12 := by
  -- The set of $k$ such that $2005$ is in $S_k$ is the set of divisors of $2004$.
  have eq1 : {k | 0 < k ∧ 2005 ∈ S k} = Nat.divisors 2004 := by
    ext k
    simp
    rw [hS]
    apply Iff.intro <;> intro h
    -- when 2005 ∈ S k
    . obtain ⟨_, n, hn⟩ := h
      replace hn : 2004 = k * n := by linarith only [hn]
      have h1 : k ∣ 2004 := by
        use n
      exact h1
    -- when k is a divisor of 2004
    . refine ⟨?_, ?_⟩
      -- show that 0 < k
      . obtain ⟨n, hn⟩ := h
        contrapose! hn
        replace hn : k = 0 := by linarith only [hn]
        rw [hn]
        norm_num
      -- show that 2005 ∈ S k
      . obtain ⟨n, hn⟩ := h
        use n
        linarith only [hn]
  -- convert the problem to the number of divisors of 2004
  rw [eq1]
  rw [Set.ncard_coe_Finset]
  -- calculate the number of divisors of 4
  have div4 : (Nat.divisors 4).card = 3 := by
    -- actually, show that the divisors of 4 are {1, 2, 4}
    have h : Nat.divisors 4 = {1, 2, 4} := by
      ext k
      simp
      apply Iff.intro <;> intro hk
      -- when k is a divisor of 4
      . match k with 
        | 0 => norm_num at hk ⊢ -- when k = 0
        | 1 => left; norm_num -- when k = 1
        | 2 => right; left; norm_num -- when k = 2
        | 3 => norm_num at hk -- when k = 3
        | 4 => right; right; norm_num -- when k = 4
        -- when k > 4
        | m + 5 => simp [show 5 ≤ m + 5 by linarith]; apply Nat.eq_zero_of_dvd_of_lt at hk; simp at hk
      -- when k is 1, 2, 4
      . rcases hk with h | h | h
        . rw [h]; norm_num
        . rw [h]; norm_num
        . rw [h]
    -- show that the number of divisors of 4 is 3
    rw [h]
    norm_num
  
  -- calculate the number of divisors of 3
  have div3 : (Nat.divisors 3).card = 2 := by
    have p3 : Nat.Prime 3 := by
      norm_num
    apply Nat.Prime.divisors at p3
    rw [p3]
    norm_num

  -- calculate the number of divisors of 167
  have div167 : (Nat.divisors 167).card = 2 := by
    have p167 : Nat.Prime 167 := by
      norm_num
    apply Nat.Prime.divisors at p167
    rw [p167]
    norm_num
  
  -- combine the results of the divisors of 4, 3, 167
  calc 
    (Nat.divisors 2004).card = (Nat.divisors (4 * 3 * 167)).card := by norm_num
    _ = (Nat.divisors 4).card * (Nat.divisors 3).card * (Nat.divisors 167).card := by
      apply Nat.Coprime.card_divisors_mul
      norm_num
    _ = 3 * 2 * 2 := by rw [div4, div3, div167]
    _ = 12 := by norm_num