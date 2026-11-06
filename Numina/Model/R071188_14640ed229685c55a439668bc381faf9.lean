import Mathlib

theorem number_theory_598977 : IsLeast {n | ∃ x : ℕ, 0 < x ∧ ⌊(10 ^ n / x : ℝ)⌋ = 1989} 7 := by
  constructor
  · -- First, let's prove that 7 belongs to the set
    use 5027
    all_goals norm_num
  · -- Now we need to prove minimality. So for any n in the set, 7 ≤ n.
    intro n hn
    rcases hn with ⟨x, hx_pos, h_floor⟩

    have h1 : (1989 : ℝ) ≤ (10 ^ n : ℝ) / (x : ℝ) := by
      have h2 : ⌊ (10 ^ n / x : ℝ) ⌋ = 1989 := h_floor
      have h3 : (1989 : ℝ) ≤ (10 ^ n / x : ℝ) := by
        have h4 : (⌊ (10 ^ n / x : ℝ) ⌋ : ℝ) ≤ (10 ^ n / x : ℝ) := by
          exact Int.floor_le ( (10 ^ n / x : ℝ) )
        rw [h2] at h4
        norm_num at h4 ⊢
        linarith
      exact h3

    have h4 : (10 ^ n : ℝ) / (x : ℝ) < (1990 : ℝ) := by
      have h2 : ⌊ (10 ^ n / x : ℝ) ⌋ = 1989 := h_floor
      have h5 : (10 ^ n / x : ℝ) < (⌊ (10 ^ n / x : ℝ) ⌋ + 1 : ℝ) := by
        exact Int.lt_floor_add_one ( (10 ^ n / x : ℝ) )
      rw [h2] at h5
      norm_num at h5 ⊢
      linarith

    have h5 : 1989 * x ≤ 10 ^ n := by
      have h6 : (1989 : ℝ) ≤ (10 ^ n : ℝ) / (x : ℝ) := h1
      have h7 : (x : ℝ) > 0 := by
        exact_mod_cast show (0 : ℕ) < x by omega
      have h8 : (1989 : ℝ) * (x : ℝ) ≤ (10 ^ n : ℝ) := by
        have h9 : (x : ℝ) > 0 := h7
        apply (le_div_iff₀ h9).mp at h6
        linarith
      norm_cast at h8

    have h10 : 10 ^ n < 1990 * x := by
      have h11 : (10 ^ n : ℝ) / (x : ℝ) < (1990 : ℝ) := h4
      have h7 : (x : ℝ) > 0 := by
        exact_mod_cast show (0 : ℕ) < x by omega
      have h8 : (10 ^ n : ℝ) < (1990 : ℝ) * (x : ℝ) := by
        have h9 : (x : ℝ) > 0 := h7
        apply (div_lt_iff₀ h9).mp at h11
        linarith
      norm_cast at h8

    by_contra h
    push_neg at h
    interval_cases n <;> omega