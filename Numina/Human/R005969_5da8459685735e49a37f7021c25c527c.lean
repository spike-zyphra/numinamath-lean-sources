import Mathlib
/-When a single number is added to each member of the seqence $20,50,100$, the sequence becomes expressable as $x, a x, a^{2} x$. Find $a$. -/

open Classical

theorem algebra_610932 (a t x : ℝ)
  (h1 : 20 + t = x)
  (h2 : 50 + t = a * x)
  (h3 : 100 + t = a^2 * x) : a = 5 / 3 := by
  -- First, substitute x from h1 into h2 and h3
  rw [← h1] at h2 h3

  -- Show that 20 + t ≠ 0 (denominator check)
  have H : 20 + t ≠ 0 := by
    intro H0
    rw [H0] at h1 h2 h3
    linarith

  -- Express a in terms of t using h2
  have A1 : a = (50 + t) / (20 + t) := by
    field_simp [H]
    exact h2.symm

  -- Show that 50 + t ≠ 0 (denominator check)
  have H' : 50 + t ≠ 0 := by
    intro h
    rw [A1] at h2 h3
    field_simp [H, h] at h2 h3
    linarith

  -- Express a in terms of t using h3
  have A2 : a = (100 + t) / (50 + t) := by
    field_simp [H, H']
    nlinarith [h2, h3]

  -- Set the two expressions for a equal to each other
  rw [A1] at A2

  -- Derive a quadratic equation in t
  have eq : (50 + t)^2 = (20 + t) * (100 + t) := by
    field_simp [H, H'] at A2
    apply Eq.symm
    ring_nf at A2
    linarith

  -- Solve for t = 25
  have t_eq : t = 25 := by
    ring_nf at *
    linarith [sq_nonneg (t - 25)]

  -- Substitute t = 25 back into A1 to get a = 5/3
  rw [t_eq] at A1
  norm_num at A1
  exact A1
