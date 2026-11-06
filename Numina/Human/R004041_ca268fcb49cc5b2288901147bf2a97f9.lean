import Mathlib

open Finset

namespace number_theory_232757

/- A number n is a composite if n > 1 and n is not a prime -/
def composite (n : ℕ) : Prop := ¬ Nat.Prime n ∧ n > 1

end number_theory_232757

open number_theory_232757

/- If n = x * y such that x y > 1, then n is not a prime -/
lemma not_prime_of_gt_one_and_two_dvd {n : ℕ} (h1 : ∃ x y, x ≥ 2 ∧ y ≥ 2 ∧ n = x * y) : ¬ Nat.Prime n := by
  obtain ⟨x, y, hx, hy, rfl⟩ := h1
  refine Nat.not_prime_mul ?_ ?_
  · exact Ne.symm (Nat.ne_of_lt hx)
  · exact Ne.symm (Nat.ne_of_lt hy)

/- If 2 ∣ n and n > 2, then n is a composite -/
lemma composite_of_even_of_gt_two {n : ℕ} (h1 : Even n) (h2 : n > 2) : composite n := by
  constructor
  · refine not_prime_of_gt_one_and_two_dvd ?_
    obtain ⟨m, hm⟩ := h1
    use 2, m; simp [hm]
    constructor
    · by_contra h
      simp at h
      interval_cases m
      all_goals
      · simp at hm; simp [hm] at h2
    · ring
  · exact Nat.lt_of_succ_lt h2

/- # Problem:
 1. Let $S$ be the set of natural numbers $n$ such that each of the numbers $n+1, n+3, n+4, n+5, n+6$, and $n+8$ is composite. Determine the largest number $k$ with the property: For every $n \in S$ in the set

$$
\{n, n+1, n+2, n+3, n+4, n+5, n+6, n+7, n+8, n+9\}
$$

there are at least $k$ consecutive composite numbers
Решение. Ќе докажеме дека $k=7$. -/
theorem number_theory_232757 {S : Set ℕ} (hS : S = {n | composite (n + 1) ∧ composite (n + 3) ∧ composite (n + 4) ∧ composite (n + 5) ∧ composite (n + 6) ∧ composite (n + 8)}) :
    IsGreatest {k | ∀ n ∈ S, ∃ m ∈ Icc n (n + 10 - k), ∀ i ∈ range k, composite (m + i)} 7 := by

  -- 87 ∈ S
  have hS_ne_empty : 87 ∈ S := by
    simp [hS]
    repeat' constructor
    all_goals apply not_prime_of_gt_one_and_two_dvd
    · use 2, 44; simp
    · use 3, 30; simp
    · use 7, 13; simp
    · use 2, 46; simp
    · use 3, 31; simp
    · use 5, 19; simp

  -- 0, 1 ∉ S
  have hzero_non_mem : 0 ∉ S := by simp [hS, composite]
  have hone_non_mem : 1 ∉ S := by simp [hS, composite]; norm_num

  constructor
  · -- Show that 7 ∈ {k | ∀ n ∈ S, ∃ m ∈ Icc n (n + 10 - k), ∀ i ∈ range k, composite (m + i)}
    -- For any n ∈ S, we show that there are at least 7 consecutive composite numbers in the set {n, n+1, ..., n+9}
    intro n hn
    by_cases hn₂ : Nat.Prime (n + 2)
    · -- If n + 2 is prime, then n + 2 is odd.
      have hodd : Odd (n + 2) := by
        apply Nat.Prime.odd_of_ne_two hn₂
        by_contra h
        simp at h
        rw [h] at hn
        contradiction
      -- Therefore, n + 7 and n + 9 are even, which means they are composite if they are greater than 2.
      have hcom₇ : composite (n + 7) := by
        apply composite_of_even_of_gt_two ?_ (by simp)
        suffices : Even (n + 2 + 5)
        · simp [this]
        · apply Odd.add_odd hodd
          exact Nat.odd_iff.mpr rfl
      have hcom₉ : composite (n + 9) := by
        apply composite_of_even_of_gt_two ?_ (by simp)
        suffices : Even (n + 2 + 7)
        · simp [this]
        · apply Odd.add_odd hodd
          exact Nat.odd_iff.mpr rfl
      -- Now, n + 3 - n + 9 are composite, and we can find 7 consecutive composite numbers.
      use n + 3
      constructor
      · simp
      · intro i hi
        simp at hi
        simp [hS] at hn
        obtain ⟨_, _, _, _, _, _⟩ := hn
        interval_cases i
        any_goals assumption
    · -- If n + 7 is prime, then n + 7 is odd.
      by_cases hn₇ : Nat.Prime (n + 7)
      · have hodd : Odd (n + 7) := by
          apply Nat.Prime.odd_of_ne_two hn₇
          simp
        -- Hence, n and n + 2 are even, which means they are composite if they are greater than 2.
        have hcom₂ : composite (n + 2) := by
          apply composite_of_even_of_gt_two ?_ ?_
          · suffices : Even (n + 7 - 5)
            · exact this
            · apply Nat.Odd.sub_odd hodd
              exact Nat.odd_iff.mpr rfl
          · simp
            by_contra h
            simp at h
            simp [h] at hn
            contradiction
        have hcom₀ : composite n := by
          apply composite_of_even_of_gt_two ?_ ?_
          · suffices : Even (n + 7 - 7)
            · exact this
            · apply Nat.Odd.sub_odd hodd
              exact Nat.odd_iff.mpr rfl
          · simp
            by_contra h
            simp at h
            interval_cases n
            all_goals contradiction
        -- Now, n ~ n + 6 are composite, and we can find 7 consecutive composite numbers.
        use n
        constructor
        · simp
        · intro i hi
          simp at hi
          simp [hS] at hn
          obtain ⟨_, _, _, _, _, _⟩ := hn
          interval_cases i
          any_goals assumption
      · -- If n + 2 and n + 7 are not prime, then they are composite.
        have hcom₂ : composite (n + 2) := by simp [composite, hn₂]
        have hcom₉ : composite (n + 7) := by simp [composite, hn₇]
        -- n + 1 ~ n + 7 are composite, and we can find 7 consecutive composite numbers.
        use n + 1
        constructor
        · simp
        · intro i hi
          simp at hi
          simp [hS] at hn
          obtain ⟨_, _, _, _, _, _⟩ := hn
          interval_cases i
          any_goals assumption
  · -- We show that there exists a case where there are not 8 consecutive composite numbers.
    intro k hk
    simp at hk
    -- Otherwise, since 87 ∈ S, we can find a number m such that m + i is composite for i ∈ range 8.
    obtain ⟨m, ⟨hm₁, hm₂⟩, hcom⟩ := hk 87 hS_ne_empty
    by_contra hk_gt
    simp at hk_gt
    -- Note that m + 7 ≤ 87 + 9, therefore, m ≤ 89
    have hm₂ : m ≤ 89 := by
      trans 87 + 10 - 8
      · apply le_trans hm₂; gcongr; exact hk_gt
      · simp
    -- Then, for any m ∈ [87, 89], we must have 89 is a composite.
    -- However, 89 is a prime number, which leads to a contradiction.
    interval_cases m
    · obtain ⟨hp, _⟩ : composite 89 := hcom 2 (by linarith)
      have : Nat.Prime 89 := by norm_num
      contradiction
    · obtain ⟨hp, _⟩ : composite 89 := hcom 1 (by linarith)
      have : Nat.Prime 89 := by norm_num
      contradiction
    · obtain ⟨hp, _⟩ : composite 89 := hcom 0 (by linarith)
      have : Nat.Prime 89 := by norm_num
      contradiction
