import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_34430 :
    {(a, b) : ℝ × ℝ | max (b^2 - (a - 1)/2) (a^2 + (b + 1)/2) ≤ 7/16} = {(1/4, -1/4)} := by
  ext ⟨a, b⟩
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First direction: if max x y <= 7/16, then (a,b) = (1/4, -1/4)
    intro h
    have h1 : b ^ 2 - (a - 1) / 2 ≤ 7 / 16 := by
      cases max_cases (b^2 - (a - 1)/2) (a^2 + (b + 1)/2) with
      | inl h2 =>
        linarith
      | inr h2 =>
        linarith
    have h2 : a ^ 2 + (b + 1) / 2 ≤ 7 / 16 := by
      cases max_cases (b^2 - (a - 1)/2) (a^2 + (b + 1)/2) with
      | inl h1 =>
        linarith
      | inr h1 =>
        linarith
    have ha2 : a = 1 / 4 := by 
      nlinarith [sq_nonneg (a - 1 / 4), sq_nonneg (b + 1 / 4)]
    have hb2 : b = -1 / 4 := by 
      nlinarith [sq_nonneg (a - 1 / 4), sq_nonneg (b + 1 / 4)]
    simp [ha2, hb2]
  · -- Second direction: (a,b) = (1/4, -1/4) implies max x y <= 7/16
    rintro ⟨rfl, rfl⟩
    norm_num [max_eq_left, max_eq_right]
    all_goals norm_num