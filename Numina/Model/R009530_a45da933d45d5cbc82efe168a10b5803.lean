import Mathlib

theorem algebra_19536 (f : ℝ → ℝ → ℝ) (fdef : ∀ a b, f a b = a ^ 2 + 2 * a * b + b ^ 2) :
    ∑ᶠ x ∈ {x : ℝ | f 2 x = 81}, x = -4 := by
  have h1 : {x : ℝ | f 2 x = 81} = {7, -11} := by
    ext x
    simp [fdef]
    constructor
    · -- Assume $f 2 x = 81$, prove $x \in \{7, -11\}$
      intro h
      have h2 : x ^ 2 + 4 * x - 77 = 0 := by
        nlinarith
      have h3 : (x - 7) * (x + 11) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h3) with h4 h5
      · -- Case $x - 7 = 0$
        left
        linarith
      · -- Case $x + 11 = 0$
        right
        linarith
    · -- Assume $x \in \{7, -11\}$, prove $f 2 x = 81$
      rintro (h | h)
      · -- Case $x = 7$
        rw [h]
        norm_num [fdef]
      · -- Case $x = -11$
        rw [h]
        norm_num [fdef]
  rw [h1]
  rw [finsum_mem_pair (by norm_num)]
  all_goals norm_num