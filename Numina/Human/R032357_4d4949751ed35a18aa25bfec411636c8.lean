import Mathlib

/- For a science project, Sammy observed a chipmunk and squirrel stashing acorns in holes.
The chipmunk hid 3 acorns in each of the holes it dug.
The squirrel hid 4 acorns in each of the holes it dug.
They each hid the same number of acorns, although the squirrel needed 4 fewer holes.
How many acorns did the chipmunk hide?
(A) 30 (B) 36 (C) 42 (D) 48 (E) 54
-/
theorem algebra_95410 {n : ℤ} (h : 3 * n = 4 * (n - 4)) :
3 * n = 48 := by
  -- rearrange the equation from `h` to bring everything to one side
  have h' : 4 * (n - 4) - 3 * n = 0 := by simp [h]
  -- distribute the `4` in `h'`, then group terms
  rw [mul_sub_left_distrib, sub_right_comm, ← mul_sub_right_distrib] at h'
  -- numerical simplifications
  simp at h'
  -- since `n-16=0`, `n=16`.
  have : n = 16 := (Int.add_left_inj (-16)).mp h'
  -- substitute `n=16` into the goal
  rw [this]
  rfl