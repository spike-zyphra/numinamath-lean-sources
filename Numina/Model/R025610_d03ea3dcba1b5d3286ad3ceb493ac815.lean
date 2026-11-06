import Mathlib

theorem algebra_323640 (x : ℝ) :
    ⌊x⌋^3 - ⌊x⌋^2 = x^3 - x^2 ↔ ∃ n : ℤ, x = n := by
  constructor
  · -- Assume ⌊x⌋^3 - ⌊x⌋^2 = x^3 - x^2, prove ∃ n : ℤ, x = n
    intro h_eq
    have h1 : (⌊x⌋ : ℝ) ≤ x := by
      exact Int.floor_le x
    have h2 : x < (⌊x⌋ + 1 : ℝ) := by
      exact Int.lt_floor_add_one x
    have h3 : (⌊x⌋ : ℝ) ^3 - (⌊x⌋ : ℝ) ^2 = x ^3 - x ^2 := by
      exact_mod_cast h_eq
    have h4 : (x - (⌊x⌋ : ℝ)) * (x ^ 2 + x * (⌊x⌋ : ℝ) + (⌊x⌋ : ℝ) ^ 2 - x - (⌊x⌋ : ℝ)) = 0 := by
      nlinarith [sq_nonneg (x - (⌊x⌋ : ℝ)), sq_nonneg (x - 1), sq_nonneg ((⌊x⌋ : ℝ) - 1), sq_nonneg (x ^ 2 - (⌊x⌋ : ℝ) ^ 2), sq_nonneg (x - (⌊x⌋ : ℝ)), h1, h2, h3]
    cases' (mul_eq_zero.mp h4) with h5 h6
    · -- Case h5: x - ⌊x⌋ = 0
      have hx : x = (⌊x⌋ : ℝ) := by
        linarith
      refine ⟨⌊x⌋, by
        exact_mod_cast hx⟩
    · -- Case h6: x^2 + x * ⌊x⌋ + ⌊x⌋^2 - x - ⌊x⌋ = 0
      have h7 : ⌊x⌋ ≤ (x : ℝ) := by
        exact_mod_cast h1
      have h8 : (x : ℝ) < (⌊x⌋ + 1 : ℝ) := by
        exact_mod_cast h2
      have h9 : ⌊x⌋ ≤ 1 := by
        by_contra h
        push_neg at h
        have h10 : ⌊x⌋ ≥ 2 := by omega
        have h11 : (⌊x⌋ : ℝ) ≥ (2 : ℝ) := by
          exact_mod_cast h10
        nlinarith [sq_nonneg (x + ((⌊x⌋ : ℝ) - 1) / 2), sq_nonneg (x - (⌊x⌋ : ℝ)), sq_nonneg (x - 1), sq_nonneg ((⌊x⌋ : ℝ) - 2)]
      have h10 : ⌊x⌋ ≥ 0 := by
        by_contra h
        push_neg at h
        have  h11 : ⌊x⌋ ≤ -1 := by omega
        have h12 : (⌊x⌋ : ℝ) ≤ (-1 : ℝ) := by
          exact_mod_cast h11
        nlinarith [sq_nonneg (x + ((⌊x⌋ : ℝ) - 1) / 2), sq_nonneg (x - (⌊x⌋ : ℝ)), sq_nonneg (x + 1), sq_nonneg ((⌊x⌋ : ℝ) + 1)]
      have h11 : ⌊x⌋ = 0 ∨ ⌊x⌋ = 1 := by omega
      rcases h11 with (h12 | h13)
      · -- Case n = 0
        have h14 : ⌊x⌋ = 0 := h12
        have h15 : (⌊x⌋ : ℝ) = (0 : ℝ) := by
          exact_mod_cast h14
        rw [h15] at h6
        have hx : x = 0 := by
          nlinarith [sq_nonneg (x), sq_nonneg (x - 1), h1, h2]
        refine ⟨0, by
          exact_mod_cast hx⟩
      · -- Case n = 1
        have h16 : ⌊x⌋ = 1 := h13
        have h17 : (⌊x⌋ : ℝ) = (1 : ℝ) := by
          exact_mod_cast h16
        rw [h17] at h6
        nlinarith [sq_nonneg (x - 1), sq_nonneg (x), h1, h2]
  · -- Backward direction: if ∃ n : ℤ, x = n, then the equation holds
    rintro ⟨n, hn⟩
    have h1 : ⌊x⌋ = n := by
      rw [hn]
      simp
    rw [show (⌊x⌋ : ℝ) = (n : ℝ) by
      exact_mod_cast h1
    ]
    rw [hn]
    all_goals
      ring_nf