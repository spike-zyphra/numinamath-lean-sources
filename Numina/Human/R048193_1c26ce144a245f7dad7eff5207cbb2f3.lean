import Mathlib

/-
There are some red and blue marbles in a box. We are told that there are twelve more red marbles than blue marbles, and we experimentally determine that when we pick a marble randomly we get a blue marble one quarter of the time. How many marbles are there in the box?
-/
theorem algebra_610867 {r b t: ℕ} (hr : r = b + 12) (htotal: r + b = t) (hposi: b/t = 1/(4:ℝ)) : (t = 24):= by

  -- rw all the equation to hposi and get a equation with only b.
  rw [hr] at htotal
  ring_nf at htotal
  rw [htotal.symm] at hposi

  -- solve the equation
  have : b = 6 := by
    field_simp at hposi
    norm_cast at hposi
    linarith
  rw [this] at hr
  linarith