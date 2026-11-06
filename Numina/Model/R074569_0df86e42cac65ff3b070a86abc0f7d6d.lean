import Mathlib

theorem number_theory_230368 : {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ 4 * x + 5 * y = 98}.encard = 5 := by
  have h1 : {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ 4 * x + 5 * y = 98} = {(2, 18), (7, 14), (12, 10), (17, 6), (22, 2)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- First, we show that (x, y) in the set implies it is one of our 5 pairs.
      rintro ⟨hx, hy, heq⟩
      have h2 : x ≤ 24 := by omega
      have h3 : y ≤ 19 := by omega
      -- Lean's `decide` is likely to solve this finite case analysis
      interval_cases x <;> omega
    · -- Show that these pairs satisfy the equation.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- ⟨2, 18⟩
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- ⟨7, 14⟩
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- ⟨12, 10⟩
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- ⟨17, 6⟩
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- ⟨22, 2⟩
        exact ⟨by norm_num, by norm_num, by norm_num⟩
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard]
  <;> try rfl