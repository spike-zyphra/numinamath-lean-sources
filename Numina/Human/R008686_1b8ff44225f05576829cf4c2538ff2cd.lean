import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Finprod


/-- Let $f$ be a function for which $f\left(\dfrac{x}{3}\right) = x^2 + x + 1$. Find the sum of all
values of $z$ for which $f(3z) = 7$.
\[\text {(A)}\ -1/3 \qquad \text {(B)}\ -1/9 \qquad \text {(C)}\ 0 \qquad \text {(D)}\ 5/9 \qquad
\text {(E)}\ 5/3\] -/
theorem algebra_1112 {f : ℂ → ℂ} (hf : ∀ x, f (x/3) = x^2 + x + 1) :
    ∑ᶠ z ∈ {z : ℂ | f (3*z) = 7}, z = -1/9  := by

  -- Substitute $x = 9z$ into the equation.
  replace hf (z : ℂ) : f (3*z) = 81*z^2 + 9*z + 1 := by
    calc _ = f ((9*z) / 3) := by congr 1; ring
         _ = (9*z)^2 + 9*z + 1 := by rw [hf]
         _ = 81*z^2 + 9*z + 1 := by ring

  -- The condition $f(3z) = 7$ is equivalent to $81z^2 + 9z + 1 = 7$ which has two solutions: -1/3
  -- and 2/9.
  have (z : ℂ) : f (3*z) = 7 ↔ z = -1/3 ∨ z = 2/9 := by
    rw [hf]
    constructor <;> intro h

    -- We can see this by factorizing the quadratic equation.
    · replace h : 81 * (z + 1/3) * (z - 2/9) = 0 := by
        calc _ = 81*z^2 + 9*z + (-6) := by ring
             _ = (81*z^2 + 9*z + 1) - 7 := by ring
             _ = 0 := by rw[h]; ring

      rw [mul_eq_zero, mul_eq_zero] at h
      simp only [OfNat.ofNat_ne_zero, false_or] at h
      rcases h with h | h
      · left
        calc z = (z + 1/3) - 1/3 := by ring
             _ = - 1/3 := by rw [h]; ring
      · right
        calc z = (z - 2/9) + 2/9 := by ring
             _ = 2/9 := by rw [h]; ring

    · rcases h with h | h <;> rw [h] <;> ring

  -- Therefore, the set of solutions is {-1/3, 2/9}.
  have : {z : ℂ | f (3*z) = 7} = {-1/3, 2/9} := by
    ext z
    constructor <;> intro h
    · simp_rw [this] at h
      exact h
    · simp_rw [this]
      exact h

  -- Clearly the sum of the solutions is -1/3 + 2/9 = -1/3 + 2/9 = -1/9.
  simp_rw [this]
  rw [finsum_mem_pair]
  · ring
  · by_contra!
    have : -(3 : ℂ) = 2 := by
      calc _ = 9 * (-1/(3 : ℂ)) := by ring
           _ = 9 * (2/(9 : ℂ)) := by rw [this]
            _ = (2 : ℂ) := by ring
    norm_cast at this