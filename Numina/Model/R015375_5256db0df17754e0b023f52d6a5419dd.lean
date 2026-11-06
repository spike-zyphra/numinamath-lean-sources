import Mathlib

theorem algebra_16197 (x : ℝ) :
    IsGreatest {n | ∃ x : ℝ, n = ⌊(3 * x ^ 2 + 9 * x + 17) / (3 * x ^ 2 + 9 * x + 7)⌋} 41 := by
  constructor
  · -- Show that 41 is in the set
    use -3 / 2
    norm_num
  · -- Show that 41 is greatest in the set
    intro n hn
    rcases hn with ⟨x, hx⟩
    by_contra h
    push_neg at h
    have h1 : n = ⌊(3 * x ^ 2 + 9 * x + 17) / (3 * x ^ 2 + 9 * x + 7)⌋ := by
      simpa using hx
    have h2 : ⌊(3 * x ^ 2 + 9 * x + 17) / (3 * x ^ 2 + 9 * x + 7)⌋ ≥ 42 := by
      have h3 : n > 41 := by
        omega
      have h4 : ⌊(3 * x ^ 2 + 9 * x + 17) / (3 * x ^ 2 + 9 * x + 7)⌋ > 41 := by
        omega
      omega
    -- Now that one implication (floor implies A >= floor) is possible.
    have h8 : (3 * x ^ 2 + 9 * x + 17) / (3 * x ^ 2 + 9 * x + 7) ≥ (42 : ℝ) := by
      have h2' : ⌊(3 * x ^ 2 + 9 * x + 17) / (3 * x ^ 2 + 9 * x + 7)⌋ ≥ 42 := by
          omega
      have h9 : (3 * x ^ 2 + 9 * x + 17) / (3 * x ^ 2 + 9 * x + 7) ≥ (⌊(3 * x ^ 2 + 9 * x + 17) / (3 * x ^ 2 + 9 * x + 7)⌋ : ℝ) := by
        have h10 : ⌊(3 * x ^ 2 + 9 * x + 17) / (3 * x ^ 2 + 9 * x + 7)⌋ ≤ (3 * x ^ 2 + 9 * x + 17) / (3 * x ^ 2 + 9 * x + 7) := by
          apply Int.floor_le
        have h11 : (⌊(3 * x ^ 2 + 9 * x + 17) / (3 * x ^ 2 + 9 * x + 7)⌋ : ℝ) ≤ (3 * x ^ 2 + 9 * x + 17) / (3 * x ^ 2 + 9 * x + 7) := by
          exact_mod_cast h10
        linarith
      have h10 : (⌊(3 * x ^ 2 + 9 * x + 17) / (3 * x ^ 2 + 9 * x + 7)⌋ : ℝ) ≥ (42 : ℝ) := by
        exact_mod_cast h2'
      linarith
    have h4 : 3 * x ^ 2 + 9 * x + 7 > 0 := by
      nlinarith [sq_nonneg (x + 3 / 2)]
    have h5 : (3 * x ^ 2 + 9 * x + 17) ≥ 42 * (3 * x ^ 2 + 9 * x + 7) := by
      apply (le_div_iff₀ h4).mp at h8
      linarith
    nlinarith [sq_nonneg (x + 3 / 2)]