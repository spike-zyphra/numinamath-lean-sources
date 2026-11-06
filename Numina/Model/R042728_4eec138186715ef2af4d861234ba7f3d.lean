import Mathlib

theorem algebra_93047 : IsGreatest {k : ℕ | ∃ a : ℤ, ∑ i ∈ Finset.range k, (a + i + 1) = 45} 90 := by
  constructor
  · -- Show 90 is in the set
    use -45
    native_decide
  · -- Show no number greater than 90 is in the set
    intro k hk
    rcases hk with ⟨a, ha⟩
    by_contra h
    push_neg at h
    have h1 : k ≥ 91 := by omega
    have h2 : k ≥ 91 := h1

    have eq1 : ∑ i in Finset.range k, (a + (i : ℤ) + 1) = k * a + (k * (k + 1) / 2 : ℤ) := by
      have h8 : ∀ (n : ℕ), ∑ i in Finset.range n, (a + (i : ℤ) + 1) = n * a + (n * (n + 1) / 2 : ℤ) := by
        intro n
        induction n with
        | zero =>
          simp
        | succ n ih =>
          rw [Finset.sum_range_succ, ih]
          simp [add_assoc] -- Simplify expression structure
          <;> ring_nf <;> omega -- Prove equality by norming and arithmetic
      specialize h8 k
      simpa using h8
    rw [eq1] at ha
    -- Now we need to show contradiction from the equation
    -- k * a + k * (k + 1) / 2 = 45 with k ≥ 91
    -- Multiply by 2 to clear denominator
    -- 2 * k * a + k * (k + 1) = 90
    -- Factor out k
    -- k * (2 * a + k + 1) = 90
    -- So k must divide 90
    -- But k ≥ 91 contradicts k divides 90

    have h7 : (k : ℤ) ≤ 90 := by
      by_contra h8
      push_neg at h8
      -- Let's show contradiction for k >= 91
      have eq3 : (k : ℤ) * a + (k * (k + 1) / 2 : ℤ) = 45 := ha

      have h9 : (k : ℤ) * (k + 1 : ℤ) % 2 = 0 := by
        have h10 : k % 2 = 0 ∨ k % 2 = 1 := by omega
        rcases h10 with (h10 | h10)
        · -- If k is even
          have h11 : (k : ℤ) % 2 = 0 := by
            omega
          simp [Int.add_emod, Int.mul_emod, h11]
          <;> omega
        · -- If k is odd
          have h11 : (k : ℤ) % 2 = 1 := by
            omega
          simp [Int.add_emod, Int.mul_emod, h11]
          <;> omega

      have h10 : (k * (k + 1) / 2 : ℤ) * 2 = (k : ℤ) * (k + 1 : ℤ) := by
        omega

      have h11 : (k : ℤ) * a * 2 + (k * (k + 1) : ℤ) = 90 := by
        omega

      -- Factor out k from left side
      -- k * (2*a + k + 1) = 90
      -- So k divides 90
      have h12 : (k : ℤ) ∣ (90 : ℤ) := by
        use (2 * a + k + 1)
        all_goals linarith
      -- But k ≥ 91 contradicts k divides 90
      have h13 : (k : ℤ) ≤ 90 := by
        have h14 : (k : ℤ) ∣ (90 : ℤ) := h12
        have h15 : (k : ℤ) ≤ 90 := by
          exact Int.le_of_dvd (by omega) h14
        omega
      omega
    -- Contradicts with k ≥ 91
    have h8 : (k : ℤ) ≥ (91 : ℤ) := by exact_mod_cast h1
    omega