import Mathlib
/- What is the maximum value of $-4z^2+20z-6$?-/
theorem algebra_14014  (f : ℝ → ℝ) (hf : f = fun z => -4 * z ^ 2 + 20 * z - 6) :
    IsGreatest (Set.image f (Set.univ : Set ℝ)) 19 := by
    simp
    rw [IsGreatest]
    rw [hf]
    constructor
    .
      use 2.5; simp; ring_nf
    .
      rw [mem_upperBounds]
      intro x hx
      simp at hx
      --We begin by writing $-4z^2+20z-6$ as $-(4z^2-20z+6)$. We then complete the square for $4z^2-20z+6$.
      cases hx with
      | intro w h =>
        --We know that the binomial to be squared will be in terms of $2z+b$ because $(2z)^2=4z^2$. By expanding $(2z+b)^2$, we get $4z^2+4bz+b^2$. We get that $4bz=-20z$, so $b=-5$, which gives us $(2z-5)^2=4z^2-20z+25$.
        --Therefore, $-(4z^2-20z+6)=-(4z^2-20z+25-19)=-[(2z-5)^2-19]=-(2z-5)^2+19$.
        rw [show -(4 * w ^ 2) + 20 * w - 6 = - (2 * w - 5) ^ 2 + 19 by ring_nf] at h
        --Since $(2z-5)^2$ is at least zero because it is a square of a real number, $-(2z-5)^2$ is at most 0. Therefore, the maximum value of $-4z^2+20z-6$ is $\boxed{19}$.
        have h2 : 0 ≤ (2 * w - 5) ^ 2 := by
          apply sq_nonneg (2 * w - 5)
        apply neg_nonpos_of_nonneg at h2
        linarith