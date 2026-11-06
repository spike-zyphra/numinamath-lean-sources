import Mathlib

theorem algebra_21251 : IsGreatest {x | x < 0 ∧ 99 ∣ x} (-99) := by
  constructor
  · -- Show that -99 is in the set
    exact ⟨by norm_num, by norm_num⟩
  · -- Show that -99 is an upper bound
    intro y hy
    rcases hy with ⟨h1, h2⟩
    omega