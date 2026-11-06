import Mathlib

/- Given $y=\left| x-a \right|+\left| x-b \right|+\left| x-c \right|$, $a<{}b<{}c$. Then the minimum value of $y$ is ___          ___. -/
theorem algebra_3954 (a b c : ℝ) (ha : a < b) (hb : b < c) :
    IsLeast {y | ∃ x : ℝ, y = abs (x - a) + abs (x - b) + abs (x - c)} (c - a) := by
  constructor
  · -- Show that c - a is achievable, i.e., there exists some x such that y = c - a
    use b
    have h1 : abs (b - a) = b - a := by
      apply abs_of_pos
      linarith
    have h2 : abs (b - c) = c - b := by
      have h3 : b - c < 0 := by linarith
      rw [abs_of_neg h3]
      linarith
    have h4 : abs (b - b) = 0 := by
      simp
    rw [h1, h4, h2]
    linarith
  · -- Show that for all y in the set, c - a ≤ y
    intro y
    rintro ⟨x, hx⟩
    have h1 : abs (x - a) + abs (x - b) + abs (x - c) ≥ c - a := by
      by_cases h1 : x ≥ c
      · -- Case 1: x ≥ c
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith
      · -- Case 2: x < c
        by_cases h2 : x ≥ b
        · -- Case 2a: b ≤ x < c
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_neg (by linarith)]
          linarith
        · -- Case 2b: x < b
          by_cases h3 : x ≥ a
          · -- Case 2b1: a ≤ x < b
            rw [abs_of_nonneg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith)]
            linarith
          · -- Case 2b2: x < a
            rw [abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith)]
            linarith
    linarith [h1, hx]