import Mathlib
open Real

/- (1) If the real number $x$ satisfies: for any positive number $a$, $x^{2}<1+a$, then the minimum value of $x$ is ( ).
(A) 0
(B) 1
(C) -1
(D) Does not exist -/
theorem inequalities_243621 :
  IsLeast {x : ℝ | ∀ a > 0, x^2 < 1 + a} (-1) := by
  -- it's clear that x = -1 works
  refine ⟨by simp, ?_⟩
  intro x hx
  simp at hx ⊢
  -- suppose x < -1
  by_contra! h
  -- then we can write x + c = -1 for some c > 0
  obtain ⟨c, c_pos, hc⟩ := exists_pos_add_of_lt' h
  -- this leads to a contradiction, since we also have x^2 < 1 + c
  absurd calc
    x^2 = (-1 - c)^2 := by nlinarith [hc]
    _ = 1 + 2 * c + c^2 := by ring
    _ ≥ 1 + c := by nlinarith [c_pos]
  push_neg; exact hx c c_pos