import Mathlib

theorem inequalities_600109 (a b c : ℝ) (ha : 0 < a + b + c)
    (hroots : ∃ x : ℝ, a * x ^ 2 + b * x + c = 0) :
    4 * min (min a b) c ≤ a + b + c ∧ a + b + c ≤ (9 / 4) * max (max a b) c := by
  rcases hroots with ⟨x, hx⟩
  constructor
  · -- 4 * min (min a b) c ≤ a + b + c
    by_cases h1 : a ≤ b
    · -- a ≤ b
      by_cases h2 : a ≤ c
      · -- a ≤ b ∧ a ≤ c
        have hmin : min (min a b) c = a := by
          simp [min_eq_left h1, min_eq_left h2]
        rw [hmin]
        nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (a), sq_nonneg (b - 2 * a), sq_nonneg (c - 2 * a), sq_nonneg (x - x), sq_nonneg (x), sq_nonneg ((x * a) + b / 2), sq_nonneg (x + 1), sq_nonneg (x - 1)]
      · -- a ≤ b ∧ c < a
        have hmin : min (min a b) c = c := by
          simp [min_eq_left h1, min_eq_right (show c ≤ a by nlinarith)]
        rw [hmin]
        nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (a - 2 * c), sq_nonneg (b - 2 * c), sq_nonneg (c), sq_nonneg (x - x), sq_nonneg (x), sq_nonneg ((x * a) + b / 2), sq_nonneg (x + 1), sq_nonneg (x - 1)]
    · -- b < a
      by_cases h2 : b ≤ c
      · -- b < a ∧ b ≤ c
        have hmin : min (min a b) c = b := by
          simp [min_eq_right (show b ≤ a by linarith), min_eq_left h2]
        rw [hmin]
        nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (a - 2 * b), sq_nonneg (b), sq_nonneg (c - 2 * b), sq_nonneg (x - x), sq_nonneg (x), sq_nonneg ((x * a) + b / 2), sq_nonneg (x + 1), sq_nonneg (x - 1)]
      · -- b < a ∧ c < b
        have hmin : min (min a b) c = c := by
          have hb1 : b < a := by linarith
          have hb2 : c < b := by linarith
          simp [min_eq_right (show b ≤ a by linarith), min_eq_right (show c ≤ b by linarith), show c ≤ a by linarith]
        rw [hmin]
        nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (a - 2 * c), sq_nonneg (b - 2 * c), sq_nonneg (c), sq_nonneg (x - x), sq_nonneg (x), sq_nonneg ((x * a) + b / 2), sq_nonneg (x + 1), sq_nonneg (x - 1)]
  · -- a + b + c ≤ (9 / 4) * max (max a b) c
    by_cases h1 : a ≤ b
    · -- a ≤ b
      by_cases h2 : a ≤ c
      · -- a ≤ b ∧ a ≤ c
        by_cases h3 : b ≤ c
        · -- a ≤ b ≤ c
          have hmax : max (max a b) c = c := by
            simp [max_eq_right h1, max_eq_right h3]
          rw [hmax]
          nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (x - x), sq_nonneg (x), sq_nonneg ((x * a) + b / 2), sq_nonneg (x + 1), sq_nonneg (x - 1)]
        · -- a ≤ c < b
          have hmax : max (max a b) c = b := by
            simp [max_eq_right h1, max_eq_left (show c ≤ b by linarith)]
          rw [hmax]
          nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (x - x), sq_nonneg (x), sq_nonneg ((x * a) + b / 2), sq_nonneg (x + 1), sq_nonneg (x - 1)]
      · -- a ≤ b ∧ c < a
        by_cases h3 : b ≤ c
        · -- a ≤ b ≤ c < a
          exfalso
          linarith
        · -- a ≤ b ∧ c < a ∧ c < b
          have hmax : max (max a b) c = b := by
            simp [max_eq_right h1, max_eq_left (show c ≤ b by linarith)]
          rw [hmax]
          nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (x - x), sq_nonneg (x), sq_nonneg ((x * a) + b / 2), sq_nonneg (x + 1), sq_nonneg (x - 1)]
    · -- b < a
      by_cases h2 : b ≤ c
      · -- b < a ∧ b ≤ c
        by_cases h3 : a ≤ c
        · -- b < a ∧ b ≤ c ∧ a ≤ c
          have hmax : max (max a b) c = c := by
            simp [max_eq_right (show a ≤ c by linarith), max_eq_left (show b ≤ a by linarith)]
          rw [hmax]
          nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (x - x), sq_nonneg (x), sq_nonneg ((x * a) + b / 2), sq_nonneg (x + 1), sq_nonneg (x - 1)]
        · -- b < a ∧ b ≤ c ∧ c < a
          have hmax : max (max a b) c = a := by
            simp [max_eq_left (show c ≤ a by linarith), max_eq_left (show b ≤ a by linarith)]
          rw [hmax]
          nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (x - x), sq_nonneg (x), sq_nonneg ((x * a) + b / 2), sq_nonneg (x + 1), sq_nonneg (x - 1)]
      · -- b < a ∧ c < b
        have hmax : max (max a b) c = a := by
          have hb1 : b < a := by linarith
          have hb2 : c < b := by linarith
          simp [max_eq_left (show b ≤ a by linarith), max_eq_left (show c ≤ b by linarith), show c ≤ a by linarith]
        rw [hmax]
        nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (x - x), sq_nonneg (x), sq_nonneg ((x * a) + b / 2), sq_nonneg (x + 1), sq_nonneg (x - 1)]