import Mathlib

/- Let  \[f(x) =
\begin{cases}
k(x) &\text{if }x>0, \\
-\frac1{2x}&\text{if }x< 0\\
0&\text{if }x=0.
\end{cases}
\]Find the function $k(x)$ such that $f(x)$ is its own inverse function. -/
theorem algebra_19710 {f: ℝ → ℝ}{k: ℝ → ℝ}
  (hf : ∀ x, x > 0 → f x = k x)
  (hf' : ∀ x, x < 0 → f x = -1 / (2 * x))
  (hf'' : ∀ x, x = 0 → f x = 0):
  (∀x, f (f x) = x) ↔ (∀x, x > 0 → k x = -1/(2*x)) := by
  -- by the problem statement, f is its own inverse function.
  -- that is f(f(x)) = 0 for all x.
  -- we should prove f(f(x)) = 0 iff k(x) is of some form.
  constructor
  · -- first, we prove if f is its own inverse function, then k(x) = -1/(2x)
    intro hk
    --we claim for any x>0, k(x) < 0
    have h1(x:ℝ)(xpos: 0 < x): k x < 0 := by
      -- notice that if y=-1/2x, then -1/2y = x
      let y := -(1/(2*x))
      have y_def: y = -(1/(2*x)) := rfl
      have yneg: y < 0 := by
        rw [y_def]
        have: 1/(2*x) > 0 := by
          apply div_pos (by norm_num) (by linarith [xpos])
        exact neg_neg_iff_pos.mpr this
      have hy: x = -1/(2*y) := by
        rw [y_def]; field_simp [xpos]
      -- x > 0, so k(x)=f(x), and then y < 0, it is f(y)
      rw [← hf x xpos]
      rw [hy, ← hf' y yneg]
      -- f(f(y))=y<0
      rw [hk y]
      exact yneg
    intro x hx
    -- when x>0, f(f(x))=f(kx). and k(x) < 0, so f(k(x)) = -1/(2k(x))
    have h2: x = -1/(2*(k x)) := by
      nth_rw 1 [← hk x]
      rw [hf x hx]
      rw [hf' (k x) (h1 x hx)]
    -- solve h2, k(x) is determined.
    nth_rw 2 [h2]; field_simp
  · -- this direction, we show given k, f(f(x))=x
    intro hk x
    by_cases hx: x ≤ 0
    · by_cases hxx: x = 0
      · rw [hf'' x hxx]
        rw [hf'' 0 rfl]
        exact hxx.symm
      · replace hxx: x < 0 := by
          exact lt_of_le_of_ne hx hxx
        -- when x < 0, f(x) > 0, and f(f(x)) = k(f(x))
        have h1: f x > 0 := by
          rw [hf' x hxx]
          have hh1: 1/(2*x) < 0 := by
            apply one_div_neg.mpr (by linarith [hxx])
          have hh2: -1 / (2*x) = - (1/(2*x)) := by ring
          rw [hh2]
          exact Left.neg_pos_iff.mpr hh1
        rw [hf (f x) h1]
        rw [hk (f x) h1]
        rw [hf' x hxx]
        field_simp
    · push_neg at hx
      -- when 0 < x, f(x) = k(x), f(f(x)) = f(k(x))
      have h1: k x < 0 := by
        rw [hk x hx]
        rw [neg_div]
        apply neg_neg_of_pos
        apply div_pos (by norm_num) (by linarith [hx])
      rw [hf x hx]
      rw [hf' (k x) h1]
      rw [hk x hx]
      field_simp