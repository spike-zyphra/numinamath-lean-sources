import Mathlib

/- The values of $f$, $g$, $h$ and $j$ are 5, 6, 7 and 8, but not necessarily in that order. What is the largest possible value of the sum of the four products $fg$, $gh$, $hj$ and $fj$? -/
theorem algebra_10238 : IsGreatest { z | ∃ f g h j : ℤ, Multiset.ofList [f, g, h, j] = Multiset.ofList [5, 6, 7, 8] ∧ z = f * g + g * h + h * j + f * j } 169 := by
  -- We have two goals:
  -- 1. Show that there exists a set of values for $f, g, h, j$ such that the sum of the four products is 169.
  -- 2. Show that any other set of values for $f, g, h, j$ will result in a sum of the four products that is less than or equal to 169.
  constructor
  . -- We can achieve the value of 169 by setting $f = 5, g = 6, h = 8, j = 7$.
    use 5, 6, 8, 7
    exact ⟨by decide, by norm_num⟩
  . -- We can show that any other set of values for $f, g, h, j$ will result in a sum of the four products that is less than or equal to 169.
    rintro z ⟨f, g, h, j, h1, rfl⟩
    -- We have $f + g + h + j = 26$.
    apply_fun Multiset.sum at h1
    simp [← add_assoc] at h1
    -- We have
    -- $$ (f + g + h + j) ^ 2 - (f + h - g - j) ^ 2 = 4fg + 4gh + 4hj + 4fj $$
    -- Thus it suffices to show that
    -- $$ (f + g + h + j) ^ 2 - (f + h - g - j) ^ 2 \le 26 ^ 2 $$
    suffices _ : (f + g + h + j) ^ 2 - (f + h - g - j) ^ 2 ≤ 26 ^ 2 by linarith
    -- Which follows from the fact that $(f + h - g - j)^2 \ge 0$
    simp [h1]
    exact sq_nonneg _
