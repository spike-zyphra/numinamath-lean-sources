import Mathlib

theorem algebra_608910 :
    IsLeast {q : ℚ | ∃ a b c : ℤ, a ∈ Set.Icc 1 2011 ∧ b ∈ Set.Icc 1 2011 ∧ c ∈ Set.Icc 1 2011 ∧ q = (a * b + c : ℚ) / (a + b + c)} (2 / 3 : ℚ) := by
  constructor
  · -- Show 2/3 is in the set by choosing a = 1, b = 1, c = 1.
    use 1, 1, 1
    norm_num
  · -- Show that no value smaller than 2/3 is in the set.
    intro q hq
    rcases hq with ⟨a, b, c, ha, hb, hc, hq⟩
    rcases ha with ⟨ha1, ha2⟩
    rcases hb with ⟨hb1, hb2⟩
    rcases hc with ⟨hc1, hc2⟩
    have h1 : (a * b + c : ℚ) / (a + b + c) ≥ (2 / 3 : ℚ) := by
      have h2 : (a : ℚ) ≥ (1 : ℚ) := by exact_mod_cast (show (1 : ℤ) ≤ a by linarith)
      have h3 : (b : ℚ) ≥ (1 : ℚ) := by exact_mod_cast (show (1 : ℤ) ≤ b by linarith)
      have h4 : (c : ℚ) ≥ (1 : ℚ) := by exact_mod_cast (show (1 : ℤ) ≤ c by linarith)
      apply (le_div_iff₀ (by
        have h5 : (a + b + c : ℚ) > 0 := by
          have h1' : (a : ℚ) ≥ (1 : ℚ) := by exact_mod_cast (show (1 : ℤ) ≤ a by linarith)
          have h2' : (b : ℚ) ≥ (1 : ℚ) := by exact_mod_cast (show (1 : ℤ) ≤ b by linarith)
          have h3' : (c : ℚ) ≥ (1 : ℚ) := by exact_mod_cast (show (1 : ℤ) ≤ c by linarith)
          linarith
        positivity)).mpr
      have h5 : 3 * ((a : ℚ) * (b : ℚ) + (c : ℚ)) ≥ 2 * ((a + b + c : ℚ)) := by
        nlinarith [mul_nonneg (show (0 : ℚ) ≤ (a - 1 : ℚ) by nlinarith) (show (0 : ℚ) ≤ (b - 1 : ℚ) by nlinarith), mul_nonneg (show (0 : ℚ) ≤ (a - 1 : ℚ) by nlinarith) (show (0 : ℚ) ≤ (c - 1 : ℚ) by nlinarith), mul_nonneg (show (0 : ℚ) ≤ (b - 1 : ℚ) by nlinarith) (show (0 : ℚ) ≤ (c - 1 : ℚ) by nlinarith)]
      linarith
    linarith [hq, h1]