import Mathlib


theorem number_theory_267653 :
    IsLeast {n : ℕ | ∃ x : ℕ, ⌊(10 ^ n / x : ℝ)⌋ = 1989} 7 := by
  constructor
  · -- Show 7 is in the set
    use 5026
    norm_num
  · -- Show 7 is the least
    intro n hn
    rcases hn with ⟨x, hx⟩
    by_contra h
    push_neg at h
    have h1 : n < (7 : ℕ) := by
      omega
    have eq : ⌊(10 ^ n / x : ℝ)⌋ = 1989 := by
      simpa using hx
    have h2 : (1989 : ℝ) ≤ (10 ^ n / x : ℝ) := by
      have h3 : (⌊(10 ^ n / x : ℝ)⌋ : ℝ) ≤ (10 ^ n / x : ℝ) := by
        exact Int.floor_le (10 ^ n / x : ℝ)
      have h4 : (⌊(10 ^ n / x : ℝ)⌋ : ℝ) = (1989 : ℝ) := by
        exact_mod_cast eq
      linarith
    have h3 : (10 ^ n / x : ℝ) < (1990 : ℝ) := by
      have h4 : (10 ^ n / x : ℝ) < (⌊(10 ^ n / x : ℝ)⌋ + 1 : ℝ) := by
        exact Int.lt_floor_add_one (10 ^ n / x : ℝ)
      have h5 : (⌊(10 ^ n / x : ℝ)⌋ : ℝ) = (1989 : ℝ) := by
        exact_mod_cast eq
      have h6 : (⌊(10 ^ n / x : ℝ)⌋ + 1 : ℝ) = (1990 : ℝ) := by
        rw [show (⌊(10 ^ n / x : ℝ)⌋ : ℝ) = (1989 : ℝ) by exact_mod_cast eq]
        all_goals norm_num
      nlinarith
    have hx1 : x > 0 := by
      by_contra h4
      push_neg at h4
      have h4 : x = 0 := by
        omega
      rw [h4] at eq
      norm_num at eq
    have h4 : (1989 : ℝ) * (x : ℝ) ≤ (10 ^ n : ℝ) := by
      have hx2 : (x : ℝ) > 0 := by
        exact_mod_cast hx1
      apply (le_div_iff₀ (by positivity)).mp at h2
      linarith
    have h5 : (10 ^ n : ℝ) < (1990 : ℝ) * (x : ℝ) := by
      have hx2 : (x : ℝ) > 0 := by
        exact_mod_cast hx1
      apply (div_lt_iff₀ (by positivity)).mp at h3
      linarith
    have h6 : 1989 * x ≤ 10 ^ n := by
      have h7 : (1989 * x : ℝ) ≤ (10 ^ n : ℝ) := by
        have h8 : (1989 : ℝ) * (x : ℝ) ≤ (10 ^ n : ℝ) := h4
        all_goals
        nlinarith
      exact_mod_cast h7
    have h7 : 10 ^ n < 1990 * x := by
      have h8 : (10 ^ n : ℝ) < (1990 : ℝ) * (x : ℝ) := by
        exact_mod_cast h5
      norm_cast at h8 ⊢
      all_goals
        nlinarith
    have h8 : n ≤ 6 := by
      omega
    interval_cases n <;> omega