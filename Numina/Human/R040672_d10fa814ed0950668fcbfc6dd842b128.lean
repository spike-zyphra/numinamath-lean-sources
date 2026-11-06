import Mathlib

open Real Set

/- 9. (16 points) Given the function

$$

f(x)=a \cos x+b \cos 2 x+c \cos 3 x,

$$


and $f(x) \geqslant-1$ always holds. Find the maximum value of $a-b+c$. -/
theorem inequalities_293739 :
  IsGreatest {a - b + c|(a: ℝ) (b : ℝ) (c : ℝ) (_ : ∀ (x : ℝ), a * cos x + b * cos (2 * x) + c * cos (3 * x) ≥ -1 )} 1
     := by
  constructor
    -- we'll prove 1 belongs to the set by using a = 1, b = 0, c = 0, the required inequality reduces to cos x ≥ -1 which is obvious
  . use 1, 0, 0
    simp only [sub_zero, add_zero, one_mul, zero_mul, ge_iff_le, exists_prop, and_true]
    rintro x
    exact neg_one_le_cos x
    -- next we'll prove 1 is an upper bound, use the equation on x = π
  . rintro x ⟨a, b, c, h, hx⟩
    replace h := h π
    -- the cos values are computed and we get -a + b - c ≥ -1
    rw [← hx]
    simp only [cos_pi, mul_neg, mul_one, cos_two_pi, ge_iff_le] at h
    rw [show 3 * π = π + 1 * (2 * π) by ring] at h
    simp only [one_mul, cos_add_two_pi, cos_pi, mul_neg, mul_one, le_add_neg_iff_add_le,
      le_neg_add_iff_add_le] at h
    -- which means 1 ≥ a - b + c
    linarith