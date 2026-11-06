import Mathlib

theorem number_theory_3275 :
  IsLeast {k : ℕ | ∃ x : ℝ, ⌊x⌋ = 2019414 ∧ ∃ p q : ℕ, p > 0 ∧ q > 0 ∧ x / 1000 = (2019 * q + p) / q ∧ k = p + q} 58 := by
  constructor
  · -- First part: Show 58 is in the set
    use 2019000 + (17000 / 41 : ℝ)
    constructor
    · -- Show floor x = 2019414
      norm_num [Int.floor_eq_iff]
    · -- Show existence of p, q > 0 with the equation and k = p + q
      use 17, 41
      norm_num
  · -- Second part: Show that 58 is the minimum
    intro k hk
    rcases hk with ⟨x, hx1, p, q, hp, hq, hx2, hk⟩
    by_contra h
    push_neg at h
    have h1 : p + q ≤ 57 := by
      omega
    have h2 : (414 : ℝ) ≤ (1000 * (p : ℝ) / (q : ℝ)) := by
      have h3 : x / 1000 = (2019 * q + p) / q := by
        linarith [hx2]
      have h4 : x = 2019000 + (1000 * (p : ℝ) / (q : ℝ)) := by
        field_simp at h3 ⊢
        nlinarith
      have h5 : (2019414 : ℝ) ≤ x := by
        have h6 : ⌊x⌋ = (2019414 : ℤ) := by
          exact_mod_cast hx1
        have h7 : (⌊x⌋ : ℝ) ≤ x := by
          exact_mod_cast Int.floor_le x
        have h8 : (⌊x⌋ : ℝ) = (2019414 : ℝ) := by
          exact_mod_cast h6
        linarith
      rw [h4] at h5
      nlinarith
    have h3 : (1000 * (p : ℝ) / (q : ℝ) < (415 : ℝ)) := by
      have h3 : x / 1000 = (2019 * q + p) / q := by
        linarith [hx2]
      have h4 : x = 2019000 + (1000 * (p : ℝ) / (q : ℝ)) := by
        field_simp at h3 ⊢
        nlinarith
      have h6 : x < (2019415 : ℝ) := by
        have h7 : ⌊x⌋ = (2019414 : ℤ) := by
          exact_mod_cast hx1
        have h8 : x < (⌊x⌋ + 1 : ℝ) := by
          exact_mod_cast Int.lt_floor_add_one x
        have h9 : (⌊x⌋ : ℝ) = (2019414 : ℝ) := by
          exact_mod_cast h7
        nlinarith
      rw [h4] at h6
      nlinarith
    have h4 : (414 * (q : ℝ) ≤ 1000 * (p : ℝ)) := by
      have h2' : (414 : ℝ) ≤ (1000 * (p : ℝ) / (q : ℝ)) := by linarith [h2]
      apply (le_div_iff₀ (by positivity)).mp at h2'
      nlinarith
    have h5 : (1000 * (p : ℝ) < 415 * (q : ℝ)) := by
      have h3' : (1000 * (p : ℝ) / (q : ℝ) < (415 : ℝ)) := by linarith [h3]
      apply (div_lt_iff₀ (by positivity)).mp at h3'
      nlinarith
    have h6 : 414 * q ≤ 1000 * p := by
      have h7 : (414 * (q : ℝ) ≤ 1000 * (p : ℝ)) := by
        nlinarith
      norm_cast at h7 ⊢
    have h7 : 1000 * p < 415 * q := by
      have h8 : (1000 * (p : ℝ) < 415 * (q : ℝ)) := by
        nlinarith
      norm_cast at h8 ⊢
    have h8 : p ≤ 56 := by
      omega
    have h9 : q ≤ 56 := by
      omega
    interval_cases p <;> omega