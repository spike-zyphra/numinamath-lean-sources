import Mathlib
open Real


/-
Let $a$ and $b$ be real numbers such that $\frac{a b}{a^{2}+b^{2}}=\frac{1}{4}$. Find all possible values of $\frac{\left|a^{2}-b^{2}\right|}{a^{2}+b^{2}}$.
-/
theorem algebra_609133 (a b : ℝ) (h: (a*b)/(a^2 + b^2) = 1/4) : (abs (a^2-b^2))/(a^2 + b^2) = sqrt 3 / 2 := by

  -- First show that  a ≠ 0 ∨ b ≠ 0
  have hp: (a ≠ 0) ∧ (b ≠ 0) := by
    constructor
    by_contra! ha; rw [ha] at h; norm_num at h
    by_contra! hb; rw [hb] at h; norm_num at h
  
  -- Thus a^2 + b^2 ≠ 0, and the frac is well defined
  have hq: a^2 + b^2 > 0 := by
    have : a^2 > 0 := by apply sq_pos_of_ne_zero hp.left
    have : b^2 > 0 := by apply sq_pos_of_ne_zero hp.right
    linarith

  -- Simplify the assumption h
  have h': a^2 + b^2 = 4*a*b := by
    field_simp [hq] at h; linarith

  -- Core equation 1
  have h1: (a+b)^2 = 6*a*b := by
    ring_nf
    calc
      _ = (a^2 + b^2) + 2*a*b := by ring
      _ = 4*a*b + 2*a*b := by rw [h']
      _ = _ := by ring
  -- Core equation 2
  have h2: (a-b)^2 = 2*a*b := by
    ring_nf
    calc
      _ =  (a^2 + b^2) - 2*a*b := by ring
      _ = 4*a*b - 2*a*b := by rw [h']
      _ = _ := by ring
  
  -- Muliply 1 and 2 and get a new equation.
  have h1h2: (a^2-b^2)^2 = 12*(a*b)^2 := by
    calc
      _ = (a+b)^2 *  (a-b)^2 := by ring_nf
      _ = 6*a*b * 2*a*b := by
        rw [h1, h2]; ring_nf
      _ = _ := by ring
  
  -- Show that ab > 0 and thus we can take square root.
  have hab: a*b > 0 := by
    by_contra! hab
    have : a*b/(a^2 + b^2) ≤ 0 := by linarith
    have _1: 1/4 ≤ 0 := by rw [h] at this
    linarith
  
  -- Take square root to both side.
  have habs: abs (a^2 - b^2) = 2*sqrt 3 * (a*b):= by
    calc
      _ = sqrt ((a^2 - b^2)^2) := by
        symm; exact sqrt_sq_eq_abs (a^2-b^2)
      _ = sqrt (12*(a*b)^2) := by rw [h1h2]
      _ = sqrt ((2*sqrt 3 * (a*b))^2) := by
        ring_nf
        have : sqrt 3 ^ 2 = 3 := by simp
        rw [this]; ring_nf
      _ = _ := by
        apply  sqrt_sq (show 2*sqrt 3 * (a*b) ≥ 0 by positivity)

  -- Calculate the result.
  calc
    _ = 2*sqrt 3 * (a*b) / (a^2 + b^2) := by rw [habs]
    _ = 2*sqrt 3 * (a*b) / (4*a*b) := by rw [h']
    _ = sqrt 3 / 2 * (a*b) / (a*b) := by ring_nf
    _ = _ := by
      field_simp [hab]; ring_nf
