import Mathlib


theorem Inequalities_288589 : ((∀ a b : ℝ, (a < b ∧ a ≠ 0 ∧ b ≠ 0 → 1 / b < 1 / a)) → False) ∧ 
  ((∀ a b c : ℝ, (a < b → a * c < b * c)) → False) ∧ (∀ a b c : ℝ, a < b → a + c < b + c → True) 
  ∧ ((∀ a b : ℝ, (a^2 < b^2 → a < b)) → False) := by 
  constructor
  · -- first statemet
    by_contra h
    simp at h
    have h' : ∀ (a b : ℝ), (a < b → ¬a = 0 → ¬b = 0 → ¬ b⁻¹ ≥  a⁻¹) := by 
      intro a b
      obtain h := h a b
      simp
      exact h
    have hexist : ∃ (a b : ℝ), a < b ∧ ¬a = 0 ∧ ¬b = 0 ∧ a⁻¹ ≤ b⁻¹ := by 
      use -1, 1
      constructor
      linarith
      constructor
      norm_num
      constructor
      norm_num
      linarith
    refine (not_exists_of_forall_not ?_) hexist
    simp
    exact h
  · -- second statement
    constructor
    by_contra h
    have hexist : ∃ (a b c: ℝ), a < b ∧  a * c ≥  b * c:= by 
      use -1, 1, 0
      constructor
      linarith
      simp
    refine (not_exists_of_forall_not ?_) hexist
    simp
    intro a b hab c
    exact h a b c hab
    -- third statement
    constructor
    intro a b c hab h
    trivial
    -- forth statement
    by_contra h
    have hexist : ∃ (a b : ℝ), a^2 < b^2 ∧  a ≥ b := by 
      use 0, -1
      constructor
      linarith
      linarith
    refine (not_exists_of_forall_not ?_) hexist
    simp
    exact h
  
