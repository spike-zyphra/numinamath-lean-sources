import Mathlib
theorem algebra_609061 (x : ℕ) (h : x ^ x = 2012 ^ (2012 ^ 2013)) : x = 2012 ^ 2012:= by
-- Rewrite 2013 as 1 + 2012
  rw [show 2013 = 1 + 2012 by ring] at h
  -- Simplify 2012^(1 + 2012) to 2012 * 2012^2012
  rw [show 2012 ^ (1 + 2012) = 2012 * 2012 ^ 2012 by ring] at h
  -- Let t = 2012 for cleaner notation
  set t:= 2012 with ht
  -- Prove t > 2
  have htge2 : t > 2:= by linarith
  clear_value t
  clear ht
  -- Rewrite t^(t * t^t) as (t^t)^(t^t)
  rw [show t ^ (t * t ^ t) = (t ^ t) ^ (t ^ t) by ring] at h
  -- Lemma: for any natural numbers y,z where y > 1 and y < z, we have y^y < z^z
  have h1 : ∀ y z : ℕ, y > 1 → y < z → y ^ y < z ^ z:= by
    intro y z hy hyz
    -- First prove y^y < y^z
    have h2 : y ^ y < y ^ z:= by exact (Nat.pow_lt_pow_iff_right hy).mpr hyz
    -- Then prove y^z < z^z
    have h3 : y ^ z < z ^ z:= by refine Nat.pow_lt_pow_left hyz (by omega)
    linarith
  -- Proof by contradiction
  by_contra H
  -- If x ≠ t^t, then either x < t^t or x > t^t
  replace H : x < t ^ t ∨ x > t ^ t:= by exact Nat.lt_or_gt_of_ne H
  -- Prove 2^2 < t
  have h2:= h1 2 t (by omega) (by omega)
  -- Prove 4^4 < (t^t)^(t^t)
  have h3:= h1 (2 ^ 2) (t ^ t) (by omega) (by omega)
  norm_num at h3
  -- Handle case analysis
  rcases H with H | H
  -- Case 1: x < t^t
  .
    -- Prove x > 1
    have h4 : x > 1:= by
      by_contra H1
      simp at H1
      have h4 : x ^ x ≤ 1:= by
        replace H1 : x = 0 ∨ x = 1:= by omega
        rcases H1 with H1 | H1
        all_goals
          subst x
          all_goals linarith
      linarith
    -- Derive contradiction
    have h5 : x ^ x < (t ^ t) ^ (t ^ t):= by
      apply h1 x (t ^ t) h4
      all_goals linarith
    linarith
  -- Case 2: x > t^t
  .
    -- Derive contradiction
    have h6 : x ^ x < x ^ x:= by
      have h7 : t ^ t < x:= by linarith
      have h8 : (t ^ t) ^ (t ^ t) < x ^ x:= by exact (h1 (t ^ t) x (by omega) h7)
      linarith
    linarith