import Mathlib

/- Let $a, b, c, d$ be real numbers whose sum is 0. Prove that


$$

5(ab + bc + cd) + 8(ac + ad + bd) \leq 0

$$
 -/
theorem inequalities_202989 (a b c d : ℝ) (h₀ : a + b + c + d = 0) :
    5 * (a * b + b * c + c * d) + 8 * (a * c + a * d + b * d) ≤ 0
  := by
    -- square a + b + c + d = 0 and multiply by 3
    apply_fun (3 * · ^ 2) at h₀

    -- then we get 3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) + 6 * (a * b + b * c + c * d) + 6 * (a * c + a * d + b * d) = 0
    convert_to 3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) + 6 * (a * b + b * c + c * d) + 6 * (a * c + a * d + b * d) = 0 at h₀
    · ring
    · ring

    --rearrange to extract terms in the goal
    convert_to (5 * (a * b + b * c + c * d) + 8 * (a * c + a * d + b * d)) + (a * b + b * c + c * d - 2 * (a * c + a * d + b * d) + 3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)) = 0 at h₀
    · ring

    -- then we can rewrite the goal
    have eq := eq_neg_of_add_eq_zero_left h₀
    rw [eq]

    -- proving that a negative expression is non-positive is the same as proving that its negation is non-negative
    rw [Right.neg_nonpos_iff]

    -- rearrange into squares
    convert_to 0 ≤ (a - c) ^ 2 + (a - d) ^ 2 + (b - d) ^ 2 + (a / 2 + b) ^ 2 + (b / 2 + c) ^ 2 + (c + d / 2) ^ 2 + (3 / 4) * (a ^ 2 + b ^ 2 + d ^ 2)
    · ring

    -- all terms are square, so sum is positive
    positivity