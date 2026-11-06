import Mathlib

/-Given $p$: $0 < x < 2$, $q$: $x < a$, if $p$ is a sufficient but not necessary condition for $q$, then the range of the real number $a$ is.-/
theorem algebra_9232 (a : ℝ) (p q : ℝ → Prop)
(hp : p = fun x => 0 < x ∧ x < 2) (hq : q = fun x => x < a)
(h : ∀ x, p x → q x) (_ : ∃ x, ¬ (q x → p x)) :
2 ≤ a := by
-- Prove by contradiction
  by_contra h'a; push_neg at h'a
-- Prove that $a$ is greater than $1$
  have ha := h 1
  simp [hp, hq] at ha
-- Plug in $x=(a+2)/2$ to h and derive a contradiction
  have := h ((a+2)/2); rw [hp, hq] at this; simp at this
  replace this := this (show 0<a+2 by linarith) (show (a+2)/2<2 by linarith)
  linarith