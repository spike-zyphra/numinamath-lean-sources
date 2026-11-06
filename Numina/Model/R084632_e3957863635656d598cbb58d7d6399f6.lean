import Mathlib

theorem algebra_10512 : ∑ᶠ x ∈ {x : ℝ | (3 : ℝ)^(x^2 + 4 * x + 4) = 9^(x + 2)}, x = -2 := by
  have h1 : {x : ℝ | (3 : ℝ)^(x^2 + 4 * x + 4) = 9^(x + 2)} = {-2, 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Forward implication: if $3^{x^2+4 x+4}=9^{x+2}$, then $x \in \{-2, 0\}$.
      intro h
      have h2 : (9 : ℝ) ^ (x + 2) = 3 ^ (2 * (x + 2)) := by
        rw [show (9 : ℝ) = 3 ^ (2 : ℝ) by norm_num]
        rw [← Real.rpow_mul]
        all_goals nlinarith
      rw [h2] at h
      have h3 : x^2 + 4 * x + 4 = 2 * (x + 2) := by
        apply_fun (Real.logb (3 : ℝ)) at h
        simp [Real.logb_rpow] at h ⊢
        all_goals nlinarith
      have h6 : x * (x + 2) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h6) with h7 h8
      · -- Case $x = 0$.
        right
        exact h7
      · -- Case $x + 2 = 0$, so $x = -2$.
        left
        linarith
    · -- Backward implication: if $x \in \{-2, 0\}$, then $3^{x^2+4 x+4}=9^{x+2}$.
      rintro (h | h)
      · -- Case $x = -2$.
        rw [h]
        norm_num
      · -- Case $x = 0$.
        rw [h]
        norm_num
  rw [h1]
  rw [finsum_mem_pair]
  all_goals norm_num
  all_goals norm_num