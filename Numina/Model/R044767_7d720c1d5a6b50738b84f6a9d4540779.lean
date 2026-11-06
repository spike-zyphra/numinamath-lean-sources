import Mathlib

theorem algebra_304672 (a b c : ℝ) :
    ∃ x, x ≥ a^2 + b^2 + c^2 ∧ (x = (a + b + c)^2 ∨ x = (a + b - c)^2 ∨ x = (b + c - a)^2 ∨ x = (c + a - b)^2) ∧
    ∃ y, y ≤ a^2 + b^2 + c^2 ∧ (y = (a + b + c)^2 ∨ y = (a + b - c)^2 ∨ y = (b + c - a)^2 ∨ y = (c + a - b)^2) := by

  have h1 : (a + b + c) ^ 2 + (a + b - c) ^ 2 + (b + c - a) ^ 2 + (c + a - b) ^ 2 =
      4 * (a ^ 2 + b ^ 2 + c ^ 2) := by
    ring

  have h2 : (a + b + c) ^ 2 ≥ a^2 + b^2 + c^2 ∨ (a + b - c) ^ 2 ≥ a^2 + b^2 + c^2 ∨ (b + c - a) ^ 2 ≥ a^2 + b^2 + c^2 ∨ (c + a - b) ^ 2 ≥ a^2 + b^2 + c^2 := by
    by_contra h
    push_neg at h
    nlinarith [sq_nonneg (a + b + c), sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b), h1, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]

  have h3 : (a + b + c) ^ 2 ≤ a^2 + b^2 + c^2 ∨ (a + b - c) ^ 2 ≤ a^2 + b^2 + c^2 ∨ (b + c - a) ^ 2 ≤ a^2 + b^2 + c^2 ∨ (c + a - b) ^ 2 ≤ a^2 + b^2 + c^2 := by
    by_contra h
    push_neg at h
    nlinarith [sq_nonneg (a + b + c), sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b), h1, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]

  rcases h2 with (h | h | h | h)
  · -- Case where (a + b + c) ^ 2 ≥ a^2 + b^2 + c^2
    use (a + b + c) ^ 2
    constructor
    · linarith [h]
    constructor
    · -- Show that x is one of the expressions
      left
      all_goals tauto
    · -- Let's solve for the existence of y
      rcases h3 with (h3 | h3 | h3 | h3)
      · -- Case where (a + b + c) ^ 2 ≤ a^2 + b^2 + c^2
        use (a + b + c) ^ 2
        constructor
        · linarith [h3]
        · -- Show that y is one of the expressions
          left
          all_goals tauto
      · -- Case where (a + b - c) ^ 2 ≤ a^2 + b^2 + c^2
        use (a + b - c) ^ 2
        constructor
        · linarith [h3]
        · -- Show that y is one of the expressions
          right
          left
          all_goals tauto
      · -- Case where (b + c - a) ^ 2 ≤ a^2 + b^2 + c^2
        use (b + c - a) ^ 2
        constructor
        · linarith [h3]
        · -- Show that y is one of the expressions
          right
          right
          left
          all_goals tauto
      · -- Case where (c + a - b) ^ 2 ≤ a^2 + b^2 + c^2
        use (c + a - b) ^ 2
        constructor
        · linarith [h3]
        · -- Show that y is one of the expressions
          right
          right
          right
          all_goals tauto
  · -- Case where (a + b - c) ^ 2 ≥ a^2 + b^2 + c^2
    use (a + b - c) ^ 2
    constructor
    · linarith [h]
    constructor
    · -- Show that x is one of the expressions
      right
      left
      all_goals tauto
    · -- Let's solve for the existence of y
      rcases h3 with (h3 | h3 | h3 | h3)
      · -- Case where (a + b + c) ^ 2 ≤ a^2 + b^2 + c^2
        use (a + b + c) ^ 2
        constructor
        · linarith [h3]
        · -- Show that y is one of the expressions
          left
          all_goals tauto
      · -- Case where (a + b - c) ^ 2 ≤ a^2 + b^2 + c^2
        use (a + b - c) ^ 2
        constructor
        · linarith [h3]
        · -- Show that y is one of the expressions
          right
          left
          all_goals tauto
      · -- Case where (b + c - a) ^ 2 ≤ a^2 + b^2 + c^2
        use (b + c - a) ^ 2
        constructor
        · linarith [h3]
        · -- Show that y is one of the expressions
          right
          right
          left
          all_goals tauto
      · -- Case where (c + a - b) ^ 2 ≤ a^2 + b^2 + c^2
        use (c + a - b) ^ 2
        constructor
        · linarith [h3]
        · -- Show that y is one of the expressions
          right
          right
          right
          all_goals tauto
  · -- Case where (b + c - a) ^ 2 ≥ a^2 + b^2 + c^2
    use (b + c - a) ^ 2
    constructor
    · linarith [h]
    constructor
    · -- Show that x is one of the expressions
      right
      right
      left
      all_goals tauto
    · -- Let's solve for the existence of y
      rcases h3 with (h3 | h3 | h3 | h3)
      · -- Case where (a + b + c) ^ 2 ≤ a^2 + b^2 + c^2
        use (a + b + c) ^ 2
        constructor
        · linarith [h3]
        · -- Show that y is one of the expressions
          left
          all_goals tauto
      · -- Case where (a + b - c) ^ 2 ≤ a^2 + b^2 + c^2
        use (a + b - c) ^ 2
        constructor
        · linarith [h3]
        · -- Show that y is one of the expressions
          right
          left
          all_goals tauto
      · -- Case where (b + c - a) ^ 2 ≤ a^2 + b^2 + c^2
        use (b + c - a) ^ 2
        constructor
        · linarith [h3]
        · -- Show that y is one of the expressions
          right
          right
          left
          all_goals tauto
      · -- Case where (c + a - b) ^ 2 ≤ a^2 + b^2 + c^2
        use (c + a - b) ^ 2
        constructor
        · linarith [h3]
        · -- Show that y is one of the expressions
          right
          right
          right
          all_goals tauto
  · -- Case where (c + a - b) ^ 2 ≥ a^2 + b^2 + c^2
    use (c + a - b) ^ 2
    constructor
    · linarith [h]
    constructor
    · -- Show that x is one of the expressions
      right
      right
      right
      all_goals tauto
    · -- Let's solve for the existence of y
      rcases h3 with (h3 | h3 | h3 | h3)
      · -- Case where (a + b + c) ^ 2 ≤ a^2 + b^2 + c^2
        use (a + b + c) ^ 2
        constructor
        · linarith [h3]
        · -- Show that y is one of the expressions
          left
          all_goals tauto
      · -- Case where (a + b - c) ^ 2 ≤ a^2 + b^2 + c^2
        use (a + b - c) ^ 2
        constructor
        · linarith [h3]
        · -- Show that y is one of the expressions
          right
          left
          all_goals tauto
      · -- 3
        use (b + c - a) ^ 2
        constructor
        · linarith [h3]
        · -- Show that y is one of the expressions
          right
          right
          left
          all_goals tauto
      · -- 4
        use (c + a - b) ^ 2
        constructor
        · linarith [h3]
        · -- Show that y is one of the expressions
          right
          right
          right
          all_goals tauto