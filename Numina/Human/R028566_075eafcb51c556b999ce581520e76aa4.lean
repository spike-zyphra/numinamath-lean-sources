import Mathlib

/- Let $p,$ $q,$ $r,$ $s$ be real numbers such that $p  +q + r + s = 8$ and
\[pq + pr + ps + qr + qs + rs = 12.\]Find the largest possible value of $s.$ -/
theorem algebra_11095 : IsGreatest {s : ℝ | ∃ p q r, p + q + r + s = 8 ∧ p*q + p*r + p*s + q*r + q*s + r*s = 12} (2 + 3*√2) := by
  -- Two goals:
  -- 1. Show that 2 + 3*√2 can be achieved
  -- 2. Show that no larger value can be achieved
  constructor
  . -- 2 + 3*√2 can be achieved when p = q = r = 2 - √2
    use 2 - √2, 2 - √2, 2 - √2
    -- Trivial simplification
    refine ⟨by ring, ?_⟩
    ring_nf
    norm_num

  . -- We prove s ≤ 2 + 3*√2
    rintro s ⟨p, q, r, ⟨h1, h2⟩⟩
    -- Use the identity (p + q + r + s)^2 = p^2 + q^2 + r^2 + s^2 + 2(pq + pr + ps + qr + qs + rs) to simplify h2
    replace h2 : p^2 + q^2 + r^2 + s^2 = 40 := by
      rw [show p^2 + q^2 + r^2 + s^2 = (p + q + r + s)^2 - 2 * (p*q + p*r + p*s + q*r + q*s + r*s) by ring, h1, h2]
      norm_num

    -- Cauchy-Schwarz inequality, proved by completing the square
    have h3 : 3 * (p^2 + q^2 + r^2) ≥ (p + q + r)^2 := by
      linarith only [sq_nonneg (p - q), sq_nonneg (q - r), sq_nonneg (r - p)]

    -- Plugin in h1, h2 into h3
    replace h3 : 3 * (p^2 + q^2 + r^2 + s^2 - s^2) ≥ (p + q + r + s - s)^2 := by
      simp
      exact h3
    rw [h1, h2] at h3

    -- Simplify the inequality
    replace h3 : (s - 2)^2 ≤ 18 := by linarith only [h3]
    rw [show 18 = (3*√2)^2 by ring_nf; norm_num] at h3
    replace h3 := abs_le_of_sq_le_sq' h3 (by positivity)
    linarith only [h3.2]
