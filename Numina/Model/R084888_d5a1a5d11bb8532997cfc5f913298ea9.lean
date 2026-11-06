import Mathlib

theorem algebra_154237 {z1 z2 : ℂ} (hz1 : z1 = 2 + 3 * .I) (hz2 : z2 = 5 - 7 * .I) :
    z1 + z2 = 7 - 4 * .I ∧ z1 - z2 = -3 + 10 * .I ∧ z1 * z2 = 31 + .I := by
  constructor
  · -- Proof of z1 + z2 = 7 - 4 * .I
    rw [hz1, hz2]
    ring_nf
  constructor
  · -- Proof of z1 - z2 = -3 + 10 * .I
    rw [hz1, hz2]
    ring_nf
  · -- Proof of z1 * z2 = 31 + .I
    rw [hz1, hz2]
    -- (2 + 3i) * (5 - 7i) = 2*5 + 2*(-7i) + 3i*5 + 3i*(-7i)
    -- = 10 - 14i + 15i - 21i^2
    -- = 10 + ( -14 + 15 )i + 21
    -- = 31 + i
    ring_nf
    <;> norm_num [Complex.ext_iff]
    all_goals norm_num