import Mathlib

theorem inequalities_70714
    (a b c : ℝ)
    (ha : 0 < a ∧ a < 1)
    (hb : 0 < b ∧ b < 1)
    (hc : 0 < c ∧ c < 1)
    (h : a + b + c = 2) :
    8 ≤ a * b * c / ((1 - a) * (1 - b) * (1 - c)) := by
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  rcases hc with ⟨hc1, hc2⟩
  have h1 : 0 < 1 - a := by linarith
  have h2 : 0 < 1 - b := by linarith
  have h3 : 0 < 1 - c := by linarith
  have h4 : a * b * c ≥ 8 * ((1 - a) * (1 - b) * (1 - c)) := by
    have h5 : c = 2 - a - b := by
      linarith
    rw [h5]
    have h6 : a < 1 := by linarith
    have h7 : b < 1 := by linarith
    have h8 : (2 - a - b) < 1 := by
      nlinarith
    have h9 : 0 < a := by linarith
    have h10 : 0 < b := by linarith
    have h11 : 0 < (2 - a - b) := by
      nlinarith
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - (2 - a - b)), sq_nonneg (b - (2 - a - b)), 
      mul_pos (show 0 < a by linarith) (show 0 < b by linarith),
      mul_pos (show 0 < a by linarith) (show 0 < (2 - a - b) by linarith),
      mul_pos (show 0 < b by linarith) (show 0 < (2 - a - b) by linarith),
      mul_pos (show 0 < 1 - a by linarith) (show 0 < 1 - b by linarith),
      mul_pos (show 0 < 1 - a by linarith) (show 0 < ( (2 - a - b) ) by nlinarith),
      mul_pos (show 0 < 1 - b by linarith) (show 0 < ( (2 - a - b) ) by nlinarith)
    ]
  have h6 : a * b * c / ((1 - a) * (1 - b) * (1 - c)) ≥ 8 := by
    have h7 : (1 - a) * (1 - b) * (1 - c) > 0 := by
      positivity
    apply (le_div_iff₀ h7).mpr
    linarith [h4]
  linarith [h6]