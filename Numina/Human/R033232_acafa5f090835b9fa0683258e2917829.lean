import Mathlib

/- What is the least positive integer which when divided by 5 gives a remainder of 4, when divided by 6 gives a remainder of 5, when divided by 7 gives a remainder of 6, when divided by 8 gives a remainder of 7, when divided by 9 gives a remainder of 8, and when divided by 10 gives a remainder of 9? -/
theorem number_theory_16840 : IsLeast {n : ℕ | n % 5 = 4 ∧ n % 6 = 5 ∧ n % 7 = 6 ∧ n % 8 = 7 ∧ n % 9 = 8 ∧ n % 10 = 9} 2519 := by
  -- Two goals: show 2519 satisfies the conditions and is the smallest
  constructor
  . -- Show 2519 satisfies the conditions
    -- Lean can compute this
    simp
  . -- Show 2519 is the smallest
    -- Let n be a number that satisfies the conditions
    intro n ⟨h5, h6, h7, h8, h9, h10⟩
    -- Rewrite the conditions
    -- 5 ∣ n + 1, 6 ∣ n + 1, 7 ∣ n + 1, 8 ∣ n + 1, 9 ∣ n + 1, 10 ∣ n + 1
    replace h5 : 5 ∣ n + 1 := by
      rw [← Nat.mod_add_div n 5, h5]
      ring_nf
      simp
    replace h6 : 6 ∣ n + 1 := by
      rw [← Nat.mod_add_div n 6, h6]
      ring_nf
      simp
    replace h7 : 7 ∣ n + 1 := by
      rw [← Nat.mod_add_div n 7, h7]
      ring_nf
      simp
    replace h8 : 8 ∣ n + 1 := by
      rw [← Nat.mod_add_div n 8, h8]
      ring_nf
      simp
    replace h9 : 9 ∣ n + 1 := by
      rw [← Nat.mod_add_div n 9, h9]
      ring_nf
      simp
    replace h10 : 10 ∣ n + 1 := by
      rw [← Nat.mod_add_div n 10, h10]
      ring_nf
      simp

    -- Use the property of lcm
    -- A number that is divisible by 5, 6, 7, 8, 9, and 10 is divisible by lcm(5, 6, 7, 8, 9, 10)
    have h : ∀ k ∈ ([5, 6, 7, 8, 9, 10] : Multiset ℕ), k ∣ n + 1 := by
      intro k
      simp
      intro hk
      obtain (rfl | rfl | rfl | rfl | rfl | rfl) := hk
      all_goals
        assumption
    rw [← Multiset.lcm_dvd] at h

    -- Let Lean compute the lcm
    simp [Multiset.lcm, lcm, Nat.lcm] at h

    -- Now omega can solve this
    clear * - h
    omega
