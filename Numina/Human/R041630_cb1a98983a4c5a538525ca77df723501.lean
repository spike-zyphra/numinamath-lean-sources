import Mathlib

/- 3. Given the complex number sequence $\left\{z_{n}\right\}$ satisfies $z_{1}=1, z_{n+1}=\overline{z_{n}}+1+n i(n=1,2, \cdots)$, then $z_{2015}=$ -/
theorem algebra_235856 {z : ℕ → ℂ} (hz1 : z 1 = 1)
    (hzn : ∀ n ≥ 1, z (n + 1) = starRingEnd ℂ (z n) + 1 + n * .I) :
    z 2015 = 2015 + 1007 * .I := by
  -- We have z(n + 3) = z(n + 2)* + 1 + (n + 2) * I
  --                  = (z(n + 1)* + 1 + (n + 1) * I)* + 1 + (n + 2) * I
  --                  = z(n + 1) + 1 - (n + 1) * I + 1 + (n + 2) * I
  --                  = z(n + 1) + 2 + I.
  have h n : z (n + 3) = z (n + 1) + 2 + .I := by
    rw [hzn (n + 2) (by linarith), hzn (n + 1) (by linarith)]
    simp
    ring
  -- Show that z(2 * n + 1) = 1 + n * (2 + I) for all n.
  have h2 n : z (2 * n + 1) = 1 + n * (2 + .I) := by
    -- Proof by induction.
    induction n with
    -- If n = 0 then 1 = 1z(1) = 1 + 0 * (2 + I).
    | zero => simp [hz1]
    | succ n ih =>
      -- Assume that z(2 * n + 1) = 1 + n * (2 + I) and consider n + 1:
      -- z(2 * (n + 1) + 1) = z(2 * n + 3)
      --                    = z(n + 1) + 2 + I
      --                    = 1 + n * (2 + I) + (2 + I)
      --                    = 1 + (n + 1) * (2 + I).
      rw [show 2 * (n + 1) + 1 = 2 * n + 3 by ring, h, ih]
      push_cast
      ring
  -- We get z(2015) = z(2 * 1007 + 1) = 1 + 1007 * (2 + I) = 2015 + 1007 * I.
  rw [show 2015 = 2 * 1007 + 1 by norm_num, h2]
  ring