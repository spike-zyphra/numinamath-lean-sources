import Mathlib


/- Ramanujan and Hardy played a game where they both picked a complex number. If the product of their numbers was $32-8i$, and Hardy picked $5+3i$, what number did Ramanujan pick? -/
theorem algebra_14842 {z : ℂ} (h : z * (5 + 3 * .I) = 32 - 8 * .I) :
    z = 4 - 4 * .I := by
  apply Eq.symm
  rw [Complex.ext_iff] at h ⊢
  simp_all
  constructor <;> linarith