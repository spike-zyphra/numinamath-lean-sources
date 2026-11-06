import Mathlib


theorem algebra_171997 (f : ℝ → ℝ) (hf : f = fun x => (2 * x ^ 3 - 6 * x ^ 2 + 13 * x + 10) / (2 * x ^ 2 - 9 * x)) :
    {x : ℕ | 0 < x ∧ ∃ k : ℤ, f x = k} = {5, 10} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, hf]
  constructor
  · -- First direction: if x is in the set, then x ∈ {5, 10}
    rintro ⟨hx_pos, k, hk⟩
    have h1 : (2 * (x : ℝ) ^ 3 - 6 * (x : ℝ) ^ 2 + 13 * (x : ℝ) + 10) / (2 * (x : ℝ) ^ 2 - 9 * (x : ℝ)) = (k : ℝ) := by
      simpa using hk
    have h2 : (2 * (x : ℝ) ^ 3 - 6 * (x : ℝ) ^ 2 + 13 * (x : ℝ) + 10) = (k : ℝ) * (2 * (x : ℝ) ^ 2 - 9 * (x : ℝ)) := by
      have hne : (2 * (x : ℝ) ^ 2 - 9 * (x : ℝ)) ≠ 0 := by
        by_contra h
        have h3 : (2 * (x : ℝ) ^ 2 - 9 * (x : ℝ)) = (0 : ℝ) := by linarith
        have h4 : (x : ℝ) * (2 * (x : ℝ) - 9) = 0 := by
          linarith
        cases' (mul_eq_zero.mp h4) with h5 h6
        · -- x = 0
          have h7 : (x : ℝ) = 0 := by
            linarith
          have h8 : x = 0 := by
            exact_mod_cast h7
          omega
        · -- 2x - 9 = 0
          have h7 : (2 * (x : ℝ) - 9) = 0 := by
            linarith
          have h8 : (2 * (x : ℝ)) = 9 := by
            linarith
          have h9 : 2 * (x : ℝ) = 9 := by
            linarith
          have h10 : 2 * x = 9 := by
            exact_mod_cast h9
          omega
      have : (2 * (x : ℝ) ^ 3 - 6 * (x : ℝ) ^ 2 + 13 * (x : ℝ) + 10) = (k : ℝ) * (2 * (x : ℝ) ^ 2 - 9 * (x : ℝ)) := by
        field_simp [hne] at h1 ⊢
        nlinarith
      assumption
    have h3 : (2 * x ^ 3 - 6 * x ^ 2 + 13 * x + 10 : ℤ) = k * (2 * x ^ 2 - 9 * x : ℤ) := by
      have h4 : (2 * (x : ℝ) ^ 3 - 6 * (x : ℝ) ^ 2 + 13 * (x : ℝ) + 10 : ℝ) = (k : ℝ) * (2 * (x : ℝ) ^ 2 - 9 * (x : ℝ) : ℝ) := h2
      norm_cast at h4 ⊢
    have h4 : x > 0 := by exact_mod_cast hx_pos
    have h9 : (x : ℤ) ∣ 10 := by
      have h10 : (x : ℤ) ∣ (2 * x ^ 3 - 6 * x ^ 2 + 13 * x + 10 : ℤ) := by
        use k * (2 * x - 9)
        have h8 : (2 * x ^ 3 - 6 * x ^ 2 + 13 * x + 10 : ℤ) = k * (2 * x ^ 2 - 9 * x : ℤ) := h3
        nlinarith
      have h13 : (x : ℤ) ∣ (x * (2 * x ^ 2 - 6 * x + 13) : ℤ) := by
        use (2 * x ^ 2 - 6 * x + 13 : ℤ)
        all_goals
          ring
      have h14 : (x : ℤ) ∣ ((2 * x ^ 3 - 6 * x ^ 2 + 13 * x + 10 : ℤ) - (x * (2 * x ^ 2 - 6 * x + 13) : ℤ)) := by
        exact Int.dvd_sub h10 h13
      have h15 : ((2 * x ^ 3 - 6 * x ^ 2 + 13 * x + 10 : ℤ) - (x * (2 * x ^ 2 - 6 * x + 13) : ℤ)) = (10 : ℤ) := by
        nlinarith
      rw [h15] at h14
      exact_mod_cast h14
    have h9 : x ≤ 10 := by
      have h9 : (x : ℤ) ∣ 10 := h9
      have h10 : (x : ℤ) ≤ 10 := by
        exact Int.le_of_dvd (show (0 : ℤ) < 10 by norm_num) h9
      omega
    interval_cases x <;> try { norm_num at h3; all_goals omega }
  · -- Second direction: if x ∈ {5, 10}, then x is in the set
    rintro (rfl | rfl)
    · -- x = 5
      constructor
      · norm_num
      · use 35
        norm_num
    · -- x = 10
      constructor
      · norm_num
      · use 14
        norm_num