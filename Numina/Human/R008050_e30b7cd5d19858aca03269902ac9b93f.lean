import Mathlib

/-If we express $3x^2 - 6x - 2$ in the form $a(x - h)^2 + k$, then what is $a + h + k$?-/
theorem algebra_13830 {a h k : ℝ} : (∀ x, 3 * x ^ 2 - 6 * x - 2 = a * (x - h) ^ 2 + k) → 
a + h + k = -1 := by
-- Introduce the assumption and plug in special values to the assumption
  intro h0
-- Rewrite $k$ in terms of $h$
  have hk := h0 h; simp at hk; symm at hk
-- Rewrite $a$ in terms of $h$
  have ha := h0 (h+1); ring_nf at ha
  apply_fun (fun x => x - k) at ha; ring_nf at ha
  rw [hk] at ha; ring_nf at ha; symm at ha
-- Rewrite the assumption h0 and plug in $x=h-1$, then solve for $h$
  rw [hk, ha] at h0; ring_nf at h0
  have := h0 (h-1); ring_nf at this; simp at this
  apply_fun (fun x => x + h * 12 + 5) at this; ring_nf at this
  apply_fun (fun x => x / 12) at this; simp at this; symm at this
  rw [this] at hk ha; norm_num at hk ha
-- After finding out the value of $h$, $a$ and $k$, we plug them into the final goal
  rw [this, hk, ha]; norm_num