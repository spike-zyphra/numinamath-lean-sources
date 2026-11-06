import Mathlib

  theorem algebra_188807 (m : ℤ) :
    {m : ℤ | IsSquare (m^2 + 6 * m + 28) } = {6, -12} := by
  ext m
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Assume that m^2 + 6 * m + 28 is a perfect square, prove that m ∈ {6, -12}
    intro h
    rcases h with ⟨k, hk⟩
    have h1 : k^2 - (m + 3)^2 = 19 := by
      nlinarith
    have h2 : (k - (m + 3)) * (k + (m + 3)) = 19 := by
      nlinarith
      <;> ring_nf at h1 ⊢
      <;> nlinarith
    have h3 : k - (m + 3) ∣ 19 := by
      use k + (m + 3)
      all_goals linarith
    have h4 : k - (m + 3) = 1 ∨ k - (m + 3) = 19 ∨ k - (m + 3) = -1 ∨ k - (m + 3) = -19 := by
      have h5 : k - (m + 3) ∣ 19 := h3
      have h6 : k - (m + 3) ≤ 19 := by
        exact Int.le_of_dvd (by norm_num) h5
      have h7 : k - (m + 3) ≥ -19 := by
        have h8 : -(k - (m + 3)) ∣ 19 := by
          exact Int.neg_dvd.2 h5
        have h9 : -(k - (m + 3)) ≤ 19 := by
          exact Int.le_of_dvd (by norm_num) h8
        omega
      interval_cases h : k - (m + 3) <;> tauto
    rcases h4 with (h | h | h | h)
    · -- k - (m + 3) = 1
      have eq1 : k + (m + 3) = 19 := by
        nlinarith [h2, h]
      have eqk : k = 10 := by 
        omega
      have eqm : m = 6 := by
        nlinarith
      left
      exact eqm
    · -- k - (m + 3) = 19
      have eq1 : k + (m + 3) = 1 := by
        nlinarith [h2, h]
      have eqk : k = 10 := by 
        omega
      have eqm : m = -12 := by
        nlinarith
      right
      exact eqm
    · -- k - (m + 3) = -1
      have eq1 : k + (m + 3) = -19 := by
        nlinarith [h2, h]
      have eqk : k = -10 := by 
        omega
      have eqm : m = -12 := by
        nlinarith
      right
      exact eqm
    · -- k - (m + 3) = -19
      have eq1 : k + (m + 3) = -1 := by
        nlinarith [h2, h]
      have eqk : k = -10 := by 
        omega
      have eqm : m = 6 := by
        nlinarith
      left
      exact eqm
  · -- Show that {6, -12} is a subset of { m | IsSquare (m ^ 2 + 6 * m + 28) }
    rintro (h | h)
    · -- m = 6
      rw [h]
      native_decide
    · -- m = -12
      rw [h]
      native_decide