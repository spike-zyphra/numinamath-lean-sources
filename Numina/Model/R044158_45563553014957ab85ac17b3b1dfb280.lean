import Mathlib

theorem number_theory_232994 (a : ℝ) (ha : 0 < a) :
    ⌊2 * a⌋ = ⌊a⌋ + ⌊a + 1 / 2⌋ := by
  let n := ⌊a⌋
  have h1 : (n : ℝ) ≤ a := by
    exact Int.floor_le a
  have h2 : a < (n + 1 : ℝ) := by
    exact Int.lt_floor_add_one a
  by_cases h : a - (n : ℝ) < 1 / 2
  · -- Assume $a - n < 1/2$, so $a < n + 1/2$
    have h3 : ⌊2 * a⌋ = 2 * n := by
      have h4 : (n : ℝ) ≤ a := by linarith [Int.floor_le a]
      have h5 : a < (n + 1 / 2 : ℝ) := by linarith
      have h6 : (2 * n : ℝ) ≤ 2 * a := by linarith
      have h7 : 2 * a < (2 * n + 1 : ℝ) := by linarith
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> (try nlinarith)
    have h8 : ⌊a + 1 / 2⌋ = n := by
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num)
      · -- Show that $n \leq a + \frac{1}{2}$
        nlinarith
      · -- Show that $a + 1/2 < n + 1$
        nlinarith
    rw [h3]
    rw [h8]
    all_goals omega
  · -- Assume $a - n \geq 1/2$, so $a \geq n + 1/2$
    have h4 : ⌊2 * a⌋ = 2 * n + 1 := by
      have h5 : (n + 1 / 2 : ℝ) ≤ a := by linarith
      have h6 : a < (n + 1 : ℝ) := by linarith [Int.lt_floor_add_one a]
      have h7 : (2 * n + 1 : ℝ) ≤ 2 * a := by linarith
      have h8 : 2 * a < (2 * n + 2 : ℝ) := by linarith
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> (try nlinarith)
    have h9 : ⌊a + 1 / 2⌋ = n + 1 := by
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num)
      · -- Show that $n + 1 \leq a + \frac{1}{2}$
        nlinarith
      · -- Show that $a + 1/2 < n + 1 + 1$
        nlinarith
    rw [h4]
    rw [h9]
    all_goals omega