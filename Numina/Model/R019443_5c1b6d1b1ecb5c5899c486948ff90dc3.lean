import Mathlib

theorem inequalities_113970 (a b c : ℝ) (ha : 1 ≤ a ∧ a ≤ 2) (hb : 1 ≤ b ∧ b ≤ 2) (hc : 1 ≤ c ∧ c ≤ 2) :
    (2 * a - b) * (a - 2 * b) ≤ 0 ∧
    4 ≤ (a + b) * (1 / c + c / (a * b)) ∧ (a + b) * (1 / c + c / (a * b)) ≤ 5 := by
  constructor
  · -- Show that (2 * a - b) * (a - 2 * b) ≤ 0
    have h1 : 1 ≤ a := ha.1
    have h2 : a ≤ 2 := ha.2
    have h3 : 1 ≤ b := hb.1
    have h4 : b ≤ 2 := hb.2
    nlinarith
  constructor
  · -- Prove that 4 ≤ (a + b) * (1 / c + c / (a * b))
    have h1 : 1 ≤ a := ha.1
    have h2 : a ≤ 2 := ha.2
    have h3 : 1 ≤ b := hb.1
    have h4 : b ≤ 2 := hb.2
    have h5 : 1 ≤ c := hc.1
    have h6 : c ≤ 2 := hc.2
    have h7 : 0 < a := by linarith
    have h8 : 0 < b := by linarith
    have h9 : 0 < c := by linarith
    have h10 : 0 < a * b := by positivity
    have h11 : 0 < a * b * c := by positivity
    have h12 : (a + b) * (1 / c + c / (a * b)) ≥ 4 := by
      have pos1 : 0 < c := by linarith
      have pos2 : 0 < a * b := by positivity
      have pos3 : 0 < a * b * c := by positivity
      have eq1 : (a + b) * (1 / c + c / (a * b)) = ( (a + b) * (a * b + c ^ 2) ) / (a * b * c) := by
        field_simp
        <;> ring_nf
        <;> field_simp
        <;> ring
      rw [eq1]
      have pos4 : 0 < a * b * c := by positivity
      have h14 : ( (a + b) * (a * b + c ^ 2) ) ≥ 4 * (a * b * c) := by
        have h15 : ( (a + b) * (a * b + c ^ 2) ) ≥ 4 * (a * b * c) := by
          nlinarith [mul_nonneg (show 0 ≤ (a - 1) by linarith) (show 0 ≤ (b - 1) by linarith), 
              mul_nonneg (show 0 ≤ (a - 1) by linarith) (show 0 ≤ (c - 1) by linarith), 
              mul_nonneg (show 0 ≤ (b - 1) by linarith) (show 0 ≤ (c - 1) by linarith),
              sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
              mul_nonneg (show 0 ≤ (a) by linarith) (show 0 ≤ (b) by linarith),
              mul_nonneg (show 0 ≤ (a) by linarith) (show 0 ≤ (c) by linarith),
              mul_nonneg (show 0 ≤ (b) by linarith) (show 0 ≤ (c) by linarith)
          ]
        linarith
      apply (le_div_iff₀ pos4).mpr
      linarith
    linarith
  · -- Prove that (a + b) * (1 / c + c / (a * b)) ≤ 5
    have h1 : 1 ≤ a := ha.1
    have h2 : a ≤ 2 := ha.2
    have h3 : 1 ≤ b := hb.1
    have h4 : b ≤ 2 := hb.2
    have h5 : 1 ≤ c := hc.1
    have h6 : c ≤ 2 := hc.2
    have h7 : 0 < a := by linarith
    have h8 : 0 < b := by linarith
    have h9 : 0 < c := by linarith
    have h10 : 0 < a * b := by positivity
    have h11 : 0 < a * b * c := by positivity
    have h13 : (a + b) * (1 / c + c / (a * b)) ≤ 5 := by
      have pos1 : 0 < c := by linarith
      have pos2 : 0 < a * b := by positivity
      have pos3 : 0 < a * b * c := by positivity
      have eq1 : (a + b) * (1 / c + c / (a * b)) = ( (a + b) * (a * b + c ^ 2) ) / (a * b * c) := by
        field_simp
        <;> ring_nf
        <;> field_simp
        <;> ring
      rw [eq1]
      have pos4 : 0 < a * b * c := by positivity
      have h14 : ( (a + b) * (a * b + c ^ 2) ) ≤ 5 * (a * b * c) := by
        have h15 : ( (a + b) * (a * b + c ^ 2) ) ≤ 5 * (a * b * c) := by
          nlinarith [mul_nonneg (show 0 ≤ (a - 1) by linarith) (show 0 ≤ (b - 1) by linarith), 
              mul_nonneg (show 0 ≤ (a - 1) by linarith) (show 0 ≤ (c - 1) by linarith), 
              mul_nonneg (show 0 ≤ (b - 1) by linarith) (show 0 ≤ (c - 1) by linarith),
              sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
              mul_nonneg (show 0 ≤ (a) by linarith) (show 0 ≤ (b) by linarith),
              mul_nonneg (show 0 ≤ (a) by linarith) (show 0 ≤ (c) by linarith),
              mul_nonneg (show 0 ≤ (b) by linarith) (show 0 ≤ (c) by linarith)
          ]
        linarith
      apply (div_le_iff₀ pos4).mpr
      linarith
    linarith