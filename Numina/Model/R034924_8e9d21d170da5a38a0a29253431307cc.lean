import Mathlib

theorem algebra_288221 :
  {(a, b, c, d) : ℕ × ℕ × ℕ × ℕ | 
    0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    a + b + c + d = 100 ∧ Even a ∧ Even b ∧ Even c ∧ Even d ∧
    c < 10 ∧ d < 10 ∧ 12 * a + 30 * b + 52 * c = 2000} =
  {(62, 28, 8, 2), (48, 44, 2, 6)} := by
  ext ⟨a, b, c, d⟩
  simp
  constructor
  · -- Prove the forward direction
    rintro ⟨ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd, h_sum, heven_a, heven_b, heven_c, heven_d, hc1, hd1, heq⟩
    have h1 : (a : ℕ) > 0 := ha
    have h2 : (b : ℕ) > 0 := hb
    have h3 : (c : ℕ) > 0 := hc
    have h4 : (d : ℕ) > 0 := hd
    -- translate even condition
    have ha1 : a % 2 = 0 := by
      obtain ⟨k, hk⟩ := heven_a
      omega
    have hb1 : b % 2 = 0 := by
      obtain ⟨k, hk⟩ := heven_b
      omega
    have hc1' : c % 2 = 0 := by
      obtain ⟨k, hk⟩ := heven_c
      omega
    have hd1' : d % 2 = 0 := by
      obtain ⟨k, hk⟩ := heven_d
      omega
    -- bounded variables, use exhaustive search
    interval_cases c <;> interval_cases d
    <;> omega
  · -- Prove the reverse direction
    rintro (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩)
    · -- Show that (62, 28, 8, 2) satisfies all constraints.
      constructor
      · norm_num -- 0 < a
      constructor
      · norm_num -- 0 < b
      constructor
      · norm_num -- 0 < c
      constructor
      · norm_num -- 0 < d
      constructor
      · norm_num -- a ≠ b
      constructor
      · norm_num -- a ≠ c
      constructor
      · norm_num -- a ≠ d
      constructor
      · norm_num -- b ≠ c
      constructor
      · norm_num -- b ≠ d
      constructor
      · norm_num -- c ≠ d
      constructor
      · norm_num -- a + b + c + d = 100
      constructor
      · decide -- Even a
      constructor
      · decide -- Even b
      constructor
      · decide -- Even c
      constructor
      · decide -- Even d
      constructor
      · norm_num -- c < 10
      · norm_num -- d < 10
      all_goals norm_num -- 12 * a + 30 * b + 52 * c = 2000
    · -- Show that (48, 44, 2, 6) satisfies all constraints.
      constructor
      · norm_num -- 0 < a
      constructor
      · norm_num -- 0 < b
      constructor
      · norm_num -- 0 < c
      constructor
      · norm_num -- 0 < d
      constructor
      · norm_num -- a ≠ b
      constructor
      · norm_num -- a ≠ c
      constructor
      · norm_num -- a ≠ d
      constructor
      · norm_num -- b ≠ c
      constructor
      · norm_num -- b ≠ d
      constructor
      · norm_num -- c ≠ d
      constructor
      · norm_num -- a + b + c + d = 100
      constructor
      · decide -- Even a
      constructor
      · decide -- Even b
      constructor
      · decide -- Even c
      constructor
      · decide -- Even d
      constructor
      · norm_num -- c < 10
      · norm_num -- d < 10
      all_goals norm_num -- 12 * a + 30 * b + 52 * c = 2000