import Mathlib
open Real

/-
How many real numbers $x$ are solutions to the following equation?

$$
|x-1|=|x-2|+|x-3|
$$
-/
theorem algebra_611304 (x:ℝ) (h: abs (x-1) = abs (x-2) + abs (x-3)) : (x=2) ∨ (x=4) := by
  
  -- Consider all possible cases for the signs of each expression inside absolute value.

  -- The first is 1, x≤ 1 is imposible because in this case x=4, a condradiction.
  have heq: x ≥ 1 := by 
    by_contra! hc

    -- If x < 1, then we rewrite |x-1| as 1-x, and substitute into h. then for |x-2| and |x-3|.
    have habs1: |x-1| = 1-x := by
      have : x-1≤ 0 := by linarith
      calc
        _ = -(x-1) := by apply abs_of_nonpos this
        _ = -x + 1 := by ring_nf
      ring_nf
    have habs2: |x-2| = 2-x := by
      have : x-2≤ 0 := by linarith
      calc
        _ = -(x-2) := by apply abs_of_nonpos this
        _ = -x + 2 := by ring_nf
      ring_nf
    have habs3: |x-3| = 3-x := by
      have : x-3≤ 0 := by linarith
      calc
        _ = -(x-3) := by apply abs_of_nonpos this
        _ = -x + 3 := by ring_nf
      ring_nf
    rw [habs1, habs2, habs3] at h
    ring_nf at h
    have : x = 4 := by linarith
    contrapose! hc
    linarith
  
  -- 2 < x < 3 leads to solution x = 2, a condradiction.
  have heq1: x ≤ 2 ∨ x ≥ 3 := by
    by_contra!
    have habs1: |x-1| = x-1 := by apply abs_of_nonneg (by linarith)
    have habs2: |x-2| = x-2 := by apply abs_of_nonneg (by linarith)
    have habs3: |x-3| = 3-x := by
      have : x-3≤ 0 := by linarith
      calc
        _ = -(x-3) := by apply abs_of_nonpos this
        _ = -x + 3 := by ring_nf
      ring_nf
    rw [habs1, habs2, habs3] at h
    ring_nf at h
    have : x = 2 := by linarith
    contrapose! this
    linarith
  
  -- Cases the x≤ 2 and x≥ 4, we have the following two branches: x=2 or x=4, which is the result.
  rcases heq1 with hl | hr

  have : x = 2 := by
    have habs1: |x-1| = x-1 := by apply abs_of_nonneg (by linarith)
    have habs2: |x-2| = 2-x := by
      have : x-2≤ 0 := by linarith
      calc
        _ = -(x-2) := by apply abs_of_nonpos this
        _ = -x + 2 := by ring_nf
      ring_nf
    have habs3: |x-3| = 3-x := by
      have : x-3≤ 0 := by linarith
      calc
        _ = -(x-3) := by apply abs_of_nonpos this
        _ = -x + 3 := by ring_nf
      ring_nf
    rw [habs1, habs2, habs3] at h
    ring_nf at h
    linarith
  tauto

  have : x = 4 := by
    have habs1: |x-1| = x-1 := by apply abs_of_nonneg (by linarith)
    have habs2: |x-2| = x-2 := by apply abs_of_nonneg (by linarith)
    have habs3: |x-3| = x-3 := by apply abs_of_nonneg (by linarith)
    rw [habs1, habs2, habs3] at h
    ring_nf at h
    linarith
  tauto


