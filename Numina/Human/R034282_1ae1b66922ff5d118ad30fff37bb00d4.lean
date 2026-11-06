import Mathlib
set_option maxRecDepth 2000

/-Given that $x$ is a positive integer, and $0<{}\frac{2019}{x}<{}2019$. If $\frac{2019}{x}$ is an integer, find the number of possible values of $x$.-/
theorem number_theory_629350 : Set.ncard {x : ℕ | 0 < x ∧ (2019 / x : ℚ)
    ∈ Set.Ioo 0 2019 ∧ ∃ k : ℤ, 2019 / (x : ℚ) = k} = 3 := by
-- It suffices to show that the set in question is equal to the set of divisors of $2019$ greater than $1$
  suffices : {x : ℕ | 0 < x ∧ (2019 / x : ℚ) ∈ Set.Ioo 0 2019
  ∧ ∃ k : ℤ, 2019 / (x : ℚ) = k} = {x ∈ Nat.divisors 2019 | 1 < x}
  · rw [this, Set.ncard_coe_Finset]; norm_cast
-- Rewrite the goal to a membership form and prove it
  simp [Set.ext_iff, and_assoc]; intro x; constructor
  · rintro ⟨xpos, hx1, ⟨k, hk⟩⟩
    rw [div_eq_iff] at hk; norm_cast at hk
    constructor
    · zify; use k; rw [hk]; ring
    by_contra!; interval_cases x
    · simp at hk; simp [hk] at hx1
    positivity
  rintro ⟨hdvd, xgt⟩; split_ands
  · positivity
  · apply div_lt_self; norm_num
    norm_cast
  zify at hdvd; rcases hdvd with ⟨k, hk⟩
  use k; qify at hk; rw [hk, mul_div_cancel_left₀]
  positivity