import Mathlib
/-Given that the sum of several consecutive positive integers is $180$, and the smallest one among them is $n$. Find the minimum possible value of $n$.
-/
theorem number_theory_633119 : IsLeast {n: ℕ | n>0∧ (∃ m > 0 , m*(2*n+m-1)=360)} 5 := by
  constructor
  · constructor
    · norm_num
    · -- check that (5, 15) is in the set
      use 15
      all_goals norm_num

  · -- Now show minimality of 5
    intro n hn
    rcases hn with ⟨hn_pos, ⟨m, hm_pos, heq⟩⟩
    by_contra h
    push_neg at h
    -- Now n < 5
    have h1 : n < 5 := by linarith
    have h2 : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by
      interval_cases n <;> omega

    rcases h2 with (rfl | rfl | rfl | rfl)
    · -- Case n = 1
      have eq1 : m * (2 * 1 + m - 1) = 360 := heq
      simp at eq1
      -- Now we have m*(m + 1) = 360
      have h3 : m ≤ 360 := by nlinarith
      interval_cases m <;> omega

    · -- Case n = 2
      have eq1 : m * (2 * 2 + m - 1) = 360 := heq
      simp at eq1
      -- Now we have m*(m + 3) = 360
      have h3 : m ≤ 360 := by nlinarith
      interval_cases m <;> omega

    · -- Case n = 3
      have eq1 : m * (2 * 3 + m - 1) = 360 := heq
      simp at eq1
      -- Now we have m*(m + 5) = 360
      have h3 : m ≤ 360 := by nlinarith
      interval_cases m <;> omega

    · -- Case n = 4
      have eq1 : m * (2 * 4 + m - 1) = 360 := heq
      simp at eq1
      -- Now we have m*(m + 7) = 360
      have h3 : m ≤ 360 := by nlinarith
      interval_cases m <;> omega
