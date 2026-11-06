import Mathlib

theorem number_theory_323188 (a : ℝ) (ha : Irrational a) :
    ∃! line : ℝ → ℝ, (∀ x, line x = (x - a) / (line 1)) ∧
      ∃ p q : ℚ, p ≠ q ∧ line p = 0 ∧ line q = 0 := by
  use fun (_ : ℝ) => (0 : ℝ)
  constructor
  · -- Show that the zero function satisfies the required properties.
    constructor
    · -- Show that ∀ x, line x = (x - a) / (line 1)
      intro x
      simp
    · -- Show that ∃ p q : ℚ, p ≠ q ∧ line p = 0 ∧ line q = 0
      use (0 : ℚ), (1 : ℚ)
      constructor
      · -- Show that (0 : ℚ) ≠ (1 : ℚ)
        norm_num
      constructor
      · -- Show that line (0 : ℚ) = 0
        norm_num
      · -- Show that line (1 : ℚ) = 0
        norm_num
  · -- Show that our line is the *only* line satisfying these properties.
    intro line h
    rcases h with ⟨h1, ⟨p, q, hpq, hp, hq⟩⟩
    have eq0 : line p = 0 := hp
    have eq1 : line q = 0 := hq
    have eq10 : line 1 = 0 := by
      have eq2 := h1 p
      rw [eq0] at eq2
      by_cases h9 : (line 1 : ℝ) = 0
      · 
        tauto
      · 
        have eq5 : (p : ℝ) - a ≠ 0 := by
          intro h'
          have h_eq : (a : ℝ) = (p : ℝ) := by linarith
          have h10 : ¬ Irrational a := by 
            rw [h_eq] 
            simp
          contradiction
        field_simp [h9] at eq2 
        all_goals 
          tauto 
    -- We want to show `line = fun (_ : ℝ) => (0 : ℝ)`.
    -- We'll show for any x, line x = 0.
    funext x
    -- We must show `line x = 0`.
    have eq11 := h1 x 
    simp [eq10] at eq11 ⊢
    all_goals 
      linarith