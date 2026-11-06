import Mathlib

theorem algebra_18707 : IsLeast {x : ℝ | abs (5 * x - 1) = abs (3 * x + 2)} (-1 / 8):= by
  constructor
  · -- Show that -1/8 is in the set.
    dsimp
    norm_num [abs_eq_abs]
  · -- Show that -1/8 is the smallest element in the set.
    intro y hy
    dsimp at hy
    cases abs_eq_abs.1 hy with
    | inl h =>
      linarith
    | inr h =>
      linarith