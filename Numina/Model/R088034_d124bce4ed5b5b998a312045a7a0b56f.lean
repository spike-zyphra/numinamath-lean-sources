import Mathlib

theorem algebra_130618 :
    {x : ℝ | abs (2006 - abs (206 - x)) = 26} = {-1774, 2186, -1826, 2238} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert,
    Set.union_singleton]
  constructor
  · -- Forward implication: prove {x | abs (2006 - abs (206 - x)) = 26} ⊆ {-1774, 2186, -1826, 2238}
    intro h
    have h1 : abs (2006 - abs (206 - x)) = 26 := h
    cases eq_or_eq_neg_of_abs_eq h1 with
    | inl h2 =>
      have h3 : abs (206 - x) = 1980 := by linarith
      cases abs_cases (206 - x) with
      | inl h4 =>
        have h5 : x = -1774 := by linarith
        rw [h5]
        norm_num
      | inr h4 =>
        have h6 : x = 2186 := by linarith
        rw [h6]
        norm_num
    | inr h2 =>
      have h3 : abs (206 - x) = 2032 := by linarith
      cases abs_cases (206 - x) with
      | inl h4 =>
        have h5 : x = -1826 := by linarith
        rw [h5]
        norm_num
      | inr h4 =>
        have h6 : x = 2238 := by linarith
        rw [h6]
        norm_num
  · -- Reverse direction: prove {-1774, 2186, -1826, 2238} ⊆ {x | abs (2006 - abs (206 - x)) = 26}
    rintro (rfl | rfl | rfl | rfl)
    · -- Check x = -1774
      norm_num [abs]
    · -- Check x = 2186
      norm_num [abs]
    · -- Check x = -1826
      norm_num [abs]
    · -- Check x = 2238
      norm_num [abs]