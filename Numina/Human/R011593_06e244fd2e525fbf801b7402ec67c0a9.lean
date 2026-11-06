import Mathlib
open Real Set

/-
12. If the real number $a$ makes the inequality $|x-2 a|+|2 x-a| \geq a^{2}$ hold for any real number $x$, then the range of the real number $a$ is
-/
theorem inequalities_268552 (a : ℝ) :
    (∀ x : ℝ, |x - 2 * a| + |2 * x - a| ≥ a ^ 2) ↔
    a ∈ Icc (-3 / 2) (3 / 2) := by
  constructor
  · -- First direction: if the inequality holds for all x, then a ∈ [-3/2, 3/2]
    intro h
    have h1 := h (a / 2)
    have h2 : 3 * |a| / 2 ≥ a ^ 2 := by
      have h2 : |(a / 2) - 2 * a| + |2 * (a / 2) - a| ≥ a ^ 2 := h1
      have h3 : |(a / 2 : ℝ) - 2 * a| = |(-3 * a / 2)| := by
        have h4 : (a / 2 : ℝ) - 2 * a = -3 * a / 2 := by ring
        rw [h4]
      have h4 : |2 * (a / 2) - a| = 0 := by
        have h5 : (2 * (a / 2) - a : ℝ) = 0 := by ring
        rw [h5]
        simp
      rw [h3, h4] at h2
      have h6 : |(-3 * a / 2 : ℝ)| = 3 * |a| / 2 := by
        have h7 : |(-3 * a / 2 : ℝ)| = |(-3 / 2) * a| := by ring
        rw [h7]
        rw [abs_mul]
        have h8 : |(-3 / 2 : ℝ)| = 3 / 2 := by norm_num
        rw [h8]
        all_goals linarith [abs_nonneg a]
      linarith [abs_nonneg (-3 * a / 2), sq_nonneg a, h6]
    have h3 : a ≤ 3 / 2 := by
      by_cases ha : a ≥ 0
      · -- If a ≥ 0, then |a| = a, so 3a/2 ≥ a²
        rw [abs_of_nonneg ha] at h2
        nlinarith [sq_nonneg (a - 3 / 2)]
      · -- If a < 0, then |a| = -a, so -3a/2 ≥ a²
        have h4 : a < 0 := lt_of_not_ge ha
        rw [abs_of_neg h4] at h2
        nlinarith [sq_nonneg (a - 3 / 2)]
    have h4 : -3 / 2 ≤ a := by
      by_cases ha : a ≥ 0
      · -- For a ≥ 0, we have |a| = a, and 3a/2 ≥ a² implies a ∈ [0, 3/2]
        nlinarith [sq_nonneg (a - 3 / 2)]
      · -- For a < 0, we have |a| = -a, and -3a/2 ≥ a²
        have h5 : a < 0 := lt_of_not_ge ha
        rw [abs_of_neg h5] at h2
        nlinarith [sq_nonneg (a + 3 / 2)]
    exact ⟨h4, h3⟩
  · -- Second direction: if a ∈ [-3/2, 3/2], then the inequality holds for all x
    rintro ⟨h1, h2⟩
    intro x
    by_cases ha : a ≥ 0
    · -- If a ≥ 0, handle cases based on x's relation to 2a and a/2
      by_cases h : x ≥ 2 * a
      · -- Case 1: x ≥ 2a
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by nlinarith)]
        nlinarith [sq_nonneg (a - 3 / 2), sq_nonneg (x - 2 * a)]
      · -- Case 2: x < 2a, further divide into a/2 ≤ x < 2a and x < a/2
        by_cases h' : x ≥ a / 2
        · -- Case 2a: a/2 ≤ x < 2a
          rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
          nlinarith [sq_nonneg (a - 3 / 2), sq_nonneg (x - a / 2)]
        · -- Case 2b: x < a/2
          rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
          nlinarith [sq_nonneg (a - 3 / 2), sq_nonneg (x - a / 2)]
    · -- If a < 0, handle cases based on x's relation to a/2 and 2a
      have h_neg : a < 0 := by linarith
      by_cases h : x ≥ a / 2
      · -- Case 1: x ≥ a/2 (and a < 0)
        rw [abs_of_nonneg (by nlinarith), abs_of_nonneg (by nlinarith)]
        nlinarith [sq_nonneg (a + 3 / 2), sq_nonneg (x - a / 2)]
      · -- Case 2: x < a/2, further divide into 2a ≤ x < a/2 and x < 2a
        by_cases h' : x ≥ 2 * a
        · -- Case 2a: 2a ≤ x < a/2
          rw [abs_of_nonneg (by nlinarith), abs_of_nonpos (by nlinarith)]
          nlinarith [sq_nonneg (a + 3 / 2), sq_nonneg (x - 2 * a)]
        · -- Case 2b: x < 2a
          rw [abs_of_nonpos (by nlinarith), abs_of_nonpos (by nlinarith)]
          nlinarith [sq_nonneg (a + 3 / 2), sq_nonneg (x - 2 * a)]