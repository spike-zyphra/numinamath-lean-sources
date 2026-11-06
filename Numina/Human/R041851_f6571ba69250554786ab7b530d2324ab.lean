import Mathlib

open Function

/- You are trying to sink a submarine. Every second, you launch a missile at a point of your choosing on the $x$-axis. If the submarine is at that point at that time, you sink it. A firing sequence is a sequence of real numbers that specify where you will fire at each second. For example, the firing sequence $2,3,5,6, \ldots$ means that you will fire at 2 after one second, 3 after two seconds, 5 after three seconds, 6 after four seconds, and so on.
(a) [5] Suppose that the submarine starts at the origin and travels along the positive $x$-axis with an (unknown) positive integer velocity. Show that there is a firing sequence that is guaranteed to hit the submarine eventually. -/
theorem number_theory_608702 : ∃ (f : ℕ → ℝ), ∀ (v : ℕ), 1 ≤ v → (∃ t, (t > 0) ∧  f t = v * t) := by 
  -- since the definition of series in Lean, the index start at 0, not 1
  -- use the firing sequence 1, 4, 9, ...
  -- v * t express that the location of the submarine at the time t. 
  let f : ℕ → ℝ := fun x => x ^ 2
  use f
  intro v hv
  use v
  constructor
  simpa
  unfold f
  ring