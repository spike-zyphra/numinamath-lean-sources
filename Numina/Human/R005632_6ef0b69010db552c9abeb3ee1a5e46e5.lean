import Mathlib

/-Find all triples of real numbers $(a, b, c)$ such that $a^{2}+2 b^{2}-2 b c=16$ and $2 a b-c^{2}=16$.
  $(4,4,4),(-4,-4,-4)$ (need both, but order doesn't matter)-/
theorem algebra_609182 : {((a:ℝ), b, c) | a^2 + 2 * b^2 - 2 * b * c = 16 ∧ 2 * a * b - c^2 = 16} =
  {(4,4,4),(-4,-4,-4)} := by
  -- $a^{2}+2 b^{2}-2 b c$ and $2 a b-c^{2}$ are both homogeneous degree 2 polynomials in $a, b, c$,
  -- so we focus on the homogeneous equation $a^{2}+$ $2 b^{2}-2 b c=2 a b-c^{2}$, or $(a-b)^{2}+(b-c)^{2}=0$.
  apply Set.ext
  intro (a,b,c)
  simp ;constructor
  intro h
  have h1 : a ^ 2 + 2 * b ^ 2 - 2 * b * c - (2 * a * b - c ^ 2) = 0 := by linarith
  have h2 : (a - b) ^ 2 + (b - c) ^ 2 = 0 := by linarith
  -- So $a=b=c$,
  have h3 : (a - b) ^ 2 = 0 ∧ (b - c) ^ 2 = 0 := by
    refine (add_eq_zero_iff_of_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c))).mp h2
  simp at h3
  have h4 : a = (a - b) + b ∧ b = (b - c) + c := by
    ring_nf ;simp
  rw [h3.1, h3.2,zero_add,zero_add] at h4
  -- and $a^{2}=2 a b-c^{2}=16$ gives the solutions $(4,4,4)$ and $(-4,-4,-4)$.
  rw [h4.1,h4.2] at h ;ring_nf at h ;simp at h
  have : c = 4 ∨ c = -4 := by refine mul_self_eq_mul_self_iff.mp ?_ ;norm_num ;rw [← h,pow_two]
  simp [h4,this]
  intro h
  rcases h with h | h
  · simp [h] ;norm_num
  simp [h] ;norm_num