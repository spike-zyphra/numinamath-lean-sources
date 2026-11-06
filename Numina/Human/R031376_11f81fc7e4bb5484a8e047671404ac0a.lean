import Mathlib

open Real

/- $5.16 \cos ^{3} x+\cos ^{2} x-4 \cos ^{2} \frac{x}{2}=0$. -/
theorem algebra_179195 {x:ℝ}:
  (cos x)^3 + (cos x)^2 - 4 * (cos (x/2))^2 = 0 ↔
  (∃ k:ℤ, x = (2*k+1) * π) := by


  -- notice that 2 cos (x/2) ^2 = 1 + cos x
  have: 4 * (cos (x/2))^2 = 2 * (1 + cos x) := by
    rw [cos_sq (x/2)]
    ring_nf

  constructor
  · -- solve equation
    intro heq
    -- factorization
    replace heq: (1 + cos x) * ( (cos x)^2 - 2) = 0 := by
      rw [← heq, this]
      ring

    -- (cos x)^2 - 2 ≠ 0, so 1 + cos x = 0, cos x = -1
    replace: (cos x)^2 - 2 ≠ 0 := by
      apply ne_of_lt
      linarith only [cos_sq_le_one x]
    simp only [mul_eq_zero, this, or_false] at heq
    replace heq: cos x = -1 := by linarith only [heq]

    -- so x = (2k+1) pi
    rw [cos_eq_neg_one_iff] at heq
    rcases heq with ⟨k, rfl⟩
    use k
    ring

  · -- verify
    rintro ⟨k,hk⟩
    rw [this]
    replace: cos x = -1 := by
      rw [cos_eq_neg_one_iff]
      use k
      rw [hk]
      ring
    rw [this]
    ring