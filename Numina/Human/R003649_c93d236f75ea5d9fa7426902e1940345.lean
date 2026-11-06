import Mathlib

open Real Set

-- Show that 0 ≤ t^2 - 2 * t implies that t ≤ 0 or 2 ≤ t.
lemma lemma_1 {t : ℝ} (ht : 0 ≤ t^2 - 2 * t) : t ≤ 0 ∨ 2 ≤ t := by
  replace ht : 0 ≤ t * (t - 2) := by linear_combination ht
  rw [mul_nonneg_iff] at ht
  cases' ht with ht ht
  · right; linarith
  · left; linarith

-- Show that 2 * t^2 - 3 * t + 4 is decreasing on (-∞, 0].
lemma lemma_2 : AntitoneOn (fun t : ℝ => 2 * t^2 - 3 * t + 4) (Iic 0) := by
  simp [AntitoneOn]
  intro a ha b hb hab
  nlinarith

-- Show that t^2 - 2 * t is decreasing on (-∞, 0].
lemma lemma_3 : AntitoneOn (fun t : ℝ => t^2 - 2 * t) (Iic 0) := by
  simp [AntitoneOn]
  intro a ha b hb hab
  nlinarith

-- Show that 2 * t^2 - 3 * t + 4 is increasing on [2, ∞).
lemma lemma_4 : MonotoneOn (fun t : ℝ => 2 * t^2 - 3 * t + 4) (Ici 2) := by
  simp [MonotoneOn]
  intro a ha b hb hab
  nlinarith

-- Show that t^2 - 2 * t is increasing on [2, ∞).
lemma lemma_5 : MonotoneOn (fun t : ℝ => t^2 - 2 * t) (Ici 2) := by
  simp [MonotoneOn]
  intro a ha b hb hab
  nlinarith

/- Example 7 Find the minimum value of the function $f(x)=\sqrt{2 x^{2}-3 x+4}+\sqrt{x^{2}-2 x}$. -/
theorem algebra_203968 {f : ℝ → ℝ} (hf : ∀ t, f t = √(2 * t ^ 2 - 3 * t + 4) + √(t ^ 2 - 2 * t)):
    IsLeast {x | ∃ t : ℝ, 0 ≤ 2 * t^2 - 3 * t + 4 ∧ 0 ≤ t^2 - 2 * t ∧ x = f t} 2 := by
  -- Show that f(0) = 2.
  have hf0 : f 0 = 2 := by
    simp [hf]
    rw [show √4 = √(2 ^ 2) by norm_num, sqrt_sq zero_le_two]
  -- Show that f(2) = √6.
  have hf2 : f 2 = √6 := by
    simp [hf]
    norm_num
  simp only [IsLeast, mem_setOf_eq, lowerBounds, forall_exists_index, and_imp]
  constructor
  · -- Show that t = 0 satisfies f(0) = 2.
    use 0
    norm_num [hf0]
  intro x t h1 h2 heq
  -- Show that 2 ≤ f(t) for all t such that 0 ≤ t^2 - 2 * t.
  -- lemma_1 implies that t ≤ 0 or 2 ≤ t.
  rcases lemma_1 h2 with ht | ht
  · -- Assume that t ≤ 0 and show that 2 = f 0 ≤ f t.
    rw [heq, ← hf0, hf, hf]
    apply add_le_add
    · -- The function 2 * t^2 - 3 * t + 4 is decreasing for t ≤ 0.
      apply sqrt_le_sqrt
      apply lemma_2 (by simp [ht]) (by simp) ht
    · -- The function t^2 - 2 * t is decreasing for t ≤ 0.
      apply sqrt_le_sqrt
      apply lemma_3 (by simp [ht]) (by simp) ht
  · -- Assume that 2 ≤ t and show that 2 ≤ √6 = f 2 ≤ f t.
    trans √6
    · rw [show 2 = √(2 ^ 2) by simp]
      apply sqrt_le_sqrt
      norm_num
    rw [heq, ← hf2, hf, hf]
    apply add_le_add
    · -- The function 2 * t^2 - 3 * t + 4 is increasing for 2 ≤ t.
      apply sqrt_le_sqrt
      apply lemma_4 (by simp [ht]) ht ht
    · -- The function t^2 - 2 * t is increasing for 2 ≤ t.
      apply sqrt_le_sqrt
      apply lemma_5 (by simp [ht]) ht ht