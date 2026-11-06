import Mathlib

/- 12. Given that $a$ and $b$ are integers. If $a^{2}-b^{2}=2003$, then the value of $a^{2}+b^{2}$ is ( ).
(A) 2006005
(B) 2005004
(C) 2004003
(D) 2003002
(E) 2002001 -/
theorem algebra_324718 (a b : ℤ) (h : a ^ 2 - b ^ 2 = 2003) : a ^ 2 + b ^ 2 = 2006005 := by
  -- Rewrite a ^ 2 - b ^ 2 as (a + b)(a - b)
  rw [sq_sub_sq] at h
  -- 2003 is prime
  have h₀ : Prime (2003 : ℤ) := Int.prime_ofNat_iff.mpr (by norm_num)
  -- So a + b or a - b must be a unit, that is, 1 or -1
  rcases prime_mul_iff.mp (h.symm ▸ h₀) with ⟨-, h₁⟩ | ⟨h₁, -⟩
  all_goals
    -- For all cases, we can get the value of a + b and a - b, thus we can get the value of a ^ 2 + b ^ 2 using `nlinarith`
    rcases Int.isUnit_iff.mp h₁ with h₂ | h₂
    all_goals
      rw [h₂] at h
      nlinarith
