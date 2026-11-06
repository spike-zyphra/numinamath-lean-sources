import Mathlib

theorem number_theory_99259 :
    IsLeast {n | ∃ x : ℤ, ⌊(10^n / x : ℝ)⌋ = 1989} 7 := by
  constructor
  · -- Show 7 is in the set.
    use 5027
    norm_num
  · -- Show no smaller n is in the set.
    intro n hn
    rcases hn with ⟨x, hx⟩
    by_contra h
    push_neg at h
    have h1 : n ≤ 6 := by linarith
    have h2 : x ≠ 0 := by
      by_contra h0
      rw [h0] at hx
      norm_num at hx
    have h4 : n ≤ 6 := h1
    have h5 : n < 7 := by linarith
    have h6 : ⌊(10 ^ n / x : ℝ)⌋ = 1989 := hx
    -- Now we convert to integer inequalities
    have h7 : (1989 : ℝ) ≤ (10 ^ n / x : ℝ) := by
      have h8 : ⌊(10 ^ n / x : ℝ)⌋ = 1989 := h6
      have h9 : (⌊(10 ^ n / x : ℝ)⌋ : ℝ) ≤ (10 ^ n / x : ℝ) := by
        exact Int.floor_le (10 ^ n / x : ℝ)
      have h10 : (⌊(10 ^ n / x : ℝ)⌋ : ℝ) = (1989 : ℝ) := by
        exact_mod_cast h8
      nlinarith
    have h8 : (10 ^ n / x : ℝ) < (1990 : ℝ) := by
      have h6' : ⌊(10 ^ n / x : ℝ)⌋ = 1989 := h6
      have h7 : (10 ^ n / x : ℝ) < (⌊(10 ^ n / x : ℝ)⌋ + 1 : ℝ) := by
        exact Int.lt_floor_add_one (10 ^ n / x : ℝ)
      have h8 : (⌊(10 ^ n / x : ℝ)⌋ + 1 : ℝ) = (1990 : ℝ) := by
        have h9 : ⌊(10 ^ n / x : ℝ)⌋ = 1989 := h6'
        have h10 : ⌊(10 ^ n / x : ℝ)⌋ + 1 = 1990 := by
          omega
        have h11 : (⌊(10 ^ n / x : ℝ)⌋ + 1 : ℝ) = (1990 : ℝ) := by
          exact_mod_cast h10
        linarith
      linarith [h7, h8]
    have h2' : x > 0 := by
      by_contra h
      push_neg at h
      have h4 : x ≤ 0 := by linarith
      by_cases h5 : x < 0
      · -- Suppose x < 0
        have h6 : x < (0 : ℤ) := h5
        have h7 : (10 ^ n / x : ℝ) < (0 : ℝ) := by
          have h8 : (10 ^ n : ℝ) > 0 := by 
            positivity
          have h9 : (x : ℝ) < (0 : ℝ) := by exact_mod_cast h6
          apply div_neg_of_pos_of_neg
          · linarith
          · linarith
        have h7 : ⌊(10 ^ n / x : ℝ)⌋ ≤ 0 := by
          rw [Int.floor_le_iff]
          linarith [h7]
        linarith [h7, h6]
      · -- So x ≥ 0, and x ≤ 0, so x = 0 
        have h8 : x = 0 := by 
          linarith
        exfalso
        apply h2
        exact_mod_cast h8
    -- Now we clear fractions
    have h13 : (1989 * x : ℝ) ≤ (10 ^ n : ℝ) := by
      have h12 : (1989 : ℝ) ≤ (10 ^ n : ℝ) / (x : ℝ) := h7
      have hx3 : (x : ℝ) > 0 := by exact_mod_cast h2'
      have h13 : (1989 * (x : ℝ) ) ≤ (10 ^ n : ℝ) := by
        have h8 : (x : ℝ) > 0 := hx3
        apply (le_div_iff₀ h8).mp at h12
        nlinarith
      linarith
    have h14 : (1989 * x : ℤ) ≤ (10 ^ n : ℤ) := by 
      exact_mod_cast h13
    -- Now we clear fractions to integer
    have h15 : (10 ^ n : ℝ) < (1990 * x : ℝ) := by
      have h11' : (10 ^ n / x : ℝ) < (1990 : ℝ) := h8
      have hx3 : (x : ℝ) > 0 := by exact_mod_cast h2'
      have h16 : (10 ^ n : ℝ) < (1990 * (x : ℝ) ) := by
        have hx3' : (x : ℝ) > 0 := hx3
        apply (div_lt_iff₀ hx3').mp at h11'
        linarith
      linarith
    have h17 : (10 ^ n : ℤ) < (1990 * x : ℤ) := by 
      exact_mod_cast h15
    interval_cases n <;> try { 
      omega
    }