import Mathlib

open Real

/-
Given the function $f(x) = sin(2x)$, if $x₁$, $x₂$ satisfy $|f(x₁) - f(x₂)| = 2$, find the minimum value of $|x₁ - x₂|$.
-/

theorem algebra_9247
    {f : ℝ → ℝ}
    (hf : ∀ x, f x = sin (2 * x)) :
    IsLeast {x | ∃ a b, x = |a - b| ∧ |f a - f b| = 2} (Real.pi / 2) := by

  have r0 : ∀ x, -1 ≤ f x ∧ f x ≤ 1 := by
    simp [hf, neg_one_le_sin, sin_le_one]

  have r1 : ∀ a b, |f a - f b| ≤ 2 := by
    intro a b
    have : |f a - f b| ≤ |f a| + |f b| := abs_sub (f a) (f b)
    have : |f a| ≤ 1 := abs_le.mpr (r0 a)
    have : |f b| ≤ 1 := abs_le.mpr (r0 b)
    linarith

  -- Since x₁, x₂ satisfy |f(x₁) - f(x₂)| = 2, the function takes on both its maximum and minimum values.
  have r2 : ∀ a b, |f a - f b| = 2 → |f a| = 1 ∧ |f b| = 1 := by
    intro a b hab
    have : |f a - f b| ≤ |f a| + |f b| := abs_sub (f a) (f b)
    constructor
    . by_contra! hfaneq1
      have : |f a| < 1 := lt_of_le_of_ne (abs_le.mpr (r0 a)) hfaneq1
      have : |f b| ≤ 1 := abs_le.mpr (r0 b)
      linarith
    . by_contra! hfbneq1
      have : |f a| ≤ 1 := abs_le.mpr (r0 a)
      have : |f b| < 1 := lt_of_le_of_ne (abs_le.mpr (r0 b)) hfbneq1
      linarith

  -- exists a, b s.t. $|a - b| = \pi / 2$ and $|f(a) - f(b)| = 2$.
  have r3 : ∃ a b, π / 2 = |a - b| ∧ |f a - f b| = 2 := by
    use π / 4, - π / 4
    rw [hf, hf, abs_of_nonneg ?_, abs_of_nonneg ?_]
    ring_nf
    rw [← div_eq_mul_one_div,
        mul_div_left_comm, neg_one_mul, sin_neg]
    simp [one_add_one_eq_two]
    . ring_nf
      rw [← div_eq_mul_one_div,
      mul_div_left_comm, neg_one_mul, sin_neg]
      simp
    . linarith [pi_pos]

  -- for all $a$, $b$ where $|f(a) - f(b)| = 2$, we can prove $|a - b| \ge \pi / 2$.
  have r4 : ∀ x, (∃ a b, x = |a - b| ∧ |f a - f b| = 2) → x ≥ π / 2 := by
    intro x ⟨a, b, ⟨hx, hab⟩⟩
    rw [hx]
    obtain ⟨ha, hb⟩ := r2 a b hab
    have : (f a = 1 ∧ f b = -1) ∨ (f a = -1 ∧ f b = 1) := by
      rcases eq_or_eq_neg_of_abs_eq ha with ha | ha
      <;> rcases eq_or_eq_neg_of_abs_eq hb with hb | hb
      any_goals simp [ha, hb]
      any_goals rw [ha, hb, sub_self, abs_zero] at hab; linarith
    simp only [hf] at this
    rcases this with ⟨ha, hb⟩ | ⟨ha, hb⟩
    . obtain ⟨ka, hka⟩ := sin_eq_one_iff.mp ha
      obtain ⟨kb, hkb⟩ := sin_eq_neg_one_iff.mp hb
      have : a - b = (1 + 2 * (ka - kb)) * (π / 2) := by linarith
      rw [this, abs_mul, abs_of_pos (show 0 < π / 2 by linarith [pi_pos])]
      apply (le_mul_iff_one_le_left (by linarith [pi_pos])).mpr
      norm_cast
      have : |1 + 2 * (ka - kb)| ≠ 0 := abs_ne_zero.mpr (by omega)
      have : 0 ≤ |1 + 2 * (ka - kb)| := abs_nonneg (1 + 2 * (ka - kb))
      omega
    . obtain ⟨ka, hka⟩ := sin_eq_neg_one_iff.mp ha
      obtain ⟨kb, hkb⟩ := sin_eq_one_iff.mp hb
      rw [abs_sub_comm]
      have : b - a = (1 + 2 * (kb - ka)) * (π / 2) := by linarith
      rw [this, abs_mul, abs_of_pos (show 0 < π / 2 by linarith [pi_pos])]
      apply (le_mul_iff_one_le_left (by linarith [pi_pos])).mpr
      norm_cast
      have : |1 + 2 * (kb - ka)| ≠ 0 := abs_ne_zero.mpr (by omega)
      have : 0 ≤ |1 + 2 * (kb - ka)| := abs_nonneg (1 + 2 * (kb - ka))
      omega

  -- -- So the answer is: $$\boxed{\frac{\pi}{2}}$$
  exact ⟨r3, r4⟩

