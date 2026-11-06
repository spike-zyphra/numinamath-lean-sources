import Mathlib

theorem algebra_263120 (S : ℕ → ℝ) (hS : ∃ a d, ∀ n, S n = a * n + d * (n * (n - 1)) / 2)
    (hS3 : S 3 = -141) (hS35 : S 35 = 35) :
    IsLeast {x | ∃ n, x = S n} (-442) := by
  rcases hS with ⟨a, d, hS'⟩
  have eq1 : S 3 = a * 3 + d * (3 * (3 - 1)) / 2 := by
    specialize hS' 3
    simpa using hS'
  have eq2 : S 35 = a * 35 + d * (35 * (35 - 1)) / 2 := by
    specialize hS' 35
    simpa using hS'
  rw [eq1] at hS3
  rw [eq2] at hS35
  have eq3 : a + d = -47 := by
    norm_num at hS3
    nlinarith
  have eq4 : a + 17 * d = 1 := by
    norm_num at hS35
    nlinarith
  have eq5 : d = 3 := by
    nlinarith
  have eq6 : a = -50 := by
    linarith
  constructor
  · -- Show that -442 is in the set
    use 17
    have h17 : S 17 = -442 := by
      rw [hS' 17]
      rw [eq6, eq5]
      norm_num
    linarith [h17]
  · -- Show that -442 is minimal
    intro x hx
    rcases hx with ⟨n, hn⟩
    have h7 : S n = a * n + d * (n * (n - 1)) / 2 := hS' n
    rw [hn]
    have h8 : S n = -50 * n + 3 * (n * (n - 1)) / 2 := by
      rw [h7]
      rw [eq6, eq5]
      all_goals norm_num
    rw [h8]
    by_cases h9 : (n : ℝ) ≤ (17 : ℝ)
    · -- Assume n ≤ 17
      have h11 : n ≤ 17 := by
        by_contra h
        push_neg at h
        have h12 : n ≥ 18 := by omega
        have h13 : (n : ℝ) ≥ (18 : ℝ) := by
          exact_mod_cast h12
        nlinarith
      have h12 : (n : ℝ) ≤ (17 : ℝ) := by
        have h11 : n ≤ 17 := h11
        exact_mod_cast h11
      have h13 : -50 * (n : ℝ) + 3 * ((n : ℝ) * ((n : ℝ) - 1)) / 2 ≥ -442 := by
        have h14 : n ≤ 17 := h11
        have h15 : n ≥ 0 := by 
          omega
        have h116 : (n : ℝ) ≥ (0 : ℝ) := by
          have h17 : n ≥ 0 := by 
            omega
          exact_mod_cast h17
        nlinarith [sq_nonneg ((n : ℝ) - 17), sq_nonneg ((n : ℝ) - 52 / 3)]
      linarith
    · -- Assume n > 17
      have h9 : (n : ℝ) > (17 : ℝ) := by
        by_contra h
        push_neg at h
        have h11 : (n : ℝ) ≤ (17 : ℝ) := by
          linarith
        contradiction
      have h11 : n > 17 := by
        by_contra h
        push_neg at h
        have h12 : n ≤ 17 := by omega
        have h13 : (n : ℝ) ≤ (17 : ℝ) := by
          exact_mod_cast h12
        nlinarith
      have h12 : (n : ℝ) ≥ (18 : ℝ) := by
        have h11 : n > 17 := h11
        have h16 : n ≥ 18 := by omega
        exact_mod_cast h16
      have h13 : -50 * (n : ℝ) + 3 * ((n : ℝ) * ((n : ℝ) - 1)) / 2 ≥ -442 := by
        have h11 : n ≥ 18 := by omega
        have h12 : (n : ℝ) ≥ (18 : ℝ) := by
          exact_mod_cast h11
        nlinarith [sq_nonneg ((n : ℝ) - 17), sq_nonneg ((n : ℝ) - 52 / 3)]
      linarith