import Mathlib

theorem number_theory_166232 :
    IsLeast {n | ∃ x : ℕ, x > 0 ∧ ⌊(10 ^ n / x : ℝ)⌋ = 1989} 7 := by 
  constructor
  · -- First part: Prove 7 belongs to the set
    use 5026
    constructor
    · norm_num -- shows 5026 is positive
    · -- Compute the floor value
      norm_num
      <;> try { linarith }
  · -- Second part: Prove 7 is minimal
    intro n hn
    rcases hn with ⟨x, hx_pos, h_floor⟩
    by_contra h
    push_neg at h
    -- Assume n < 7, so n <= 6
    have h1 : n ≤ 6 := by linarith
    -- The equation ⌊(10 ^ n / x : ℝ)⌋ = 1989 implies 1989 ≤ (10 ^ n / x : ℝ) < 1990
    have h2 : x > 0 := hx_pos
    have h3 : (1989 : ℝ) ≤ (10 ^ n : ℝ) / (x : ℝ) := by
      have h_floor_eq : ⌊(10 ^ n / x : ℝ)⌋ = 1989 := h_floor
      have h1 : (1989 : ℝ) ≤ (10 ^ n / x : ℝ) := by
        have h2 : (⌊(10 ^ n / x : ℝ)⌋ : ℝ) ≤ (10 ^ n / x : ℝ) := by
          exact Int.floor_le (10 ^ n / x : ℝ)
        rw [h_floor_eq] at h2
        linarith
      linarith
    have h4 : (10 ^ n : ℝ) / (x : ℝ) < (1990 : ℝ) := by
      have h_floor_eq : ⌊(10 ^ n / x : ℝ)⌋ = 1989 := h_floor
      have h3 : (10 ^ n / x : ℝ) < (⌊(10 ^ n / x : ℝ)⌋ + 1 : ℝ) := by
        exact Int.lt_floor_add_one (10 ^ n / x : ℝ)
      rw [h_floor_eq] at h3
      linarith
    -- Convert inequalities to integer form
    have h5 : 1989 * x ≤ 10 ^ n := by
      have h6 : (1989 : ℝ) ≤ (10 ^ n : ℝ) / (x : ℝ) := h3
      have h7 : (x : ℝ) > 0 := by
        exact_mod_cast show (0 : ℕ) < x by linarith
      have h8 : (1989 : ℝ) * (x : ℝ) ≤ (10 ^ n : ℝ) := by
        have h9 : (10 ^ n : ℝ) / (x : ℝ) ≥ 0 := by positivity
        apply (le_div_iff₀ h7).mp at h6
        linarith
      exact_mod_cast h8
    have h10 : 10 ^ n < 1990 * x := by
      have h11 : (10 ^ n : ℝ) / (x : ℝ) < (1990 : ℝ) := h4
      have h7 : (x : ℝ) > 0 := by
        exact_mod_cast show (0 : ℕ) < x by linarith
      have h12 : (10 ^ n : ℝ) < (1990 : ℝ) * (x : ℝ) := by
        apply (div_lt_iff₀ h7).mp at h11
        linarith
      exact_mod_cast h12
    -- Now with the bounds 1989 * x ≤ 10 ^ n < 1990 * x
    -- We will show for each n <= 6, no integer x > 0 exists
    interval_cases n <;> omega