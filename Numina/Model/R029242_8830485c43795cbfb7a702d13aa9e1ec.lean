import Mathlib

theorem algebra_5885 :
    {f : ℕ → ℕ | ∀ m n, f (n + m * f n) = n * f (m + 1)} = {0, id} := by
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- Assume f satisfies the functional equation, prove f = 0 or f = id
    intro h
    have h1 : ∀ n, f n = n * f 1 := by
      intro n
      specialize h 0 n
      simp at h
      linarith
    have h2 : ∀ m, f (m * f 0) = 0 := by
      intro m
      specialize h m 0
      simp at h
      all_goals
        try { linarith }
        try { tauto }
    -- Show that f 0 = 0
    have h3 : f 0 = 0 := by
      have h4 := h1 0
      simp at h4 ⊢
      <;> omega
    -- Now analyzing for $n = 1$ and $m = 1$ in the functional equation.
    have h4 : f (1 + 1 * f 1) = 1 * f (1 + 1) := h 1 1
    have h5 : f (1 + 1 * f 1) = (1 + f 1) * f 1 := by
      have h7 : ∀ n, f n = n * f 1 := h1
      specialize h7 (1 + 1 * f 1)
      have h8 : f (1 + 1 * f 1) = (1 + 1 * f 1) * f 1 := h7
      ring_nf at h8 ⊢
      <;> omega
    -- Calculate f(2) using h1
    have h6 : f (1 + 1) = 2 * f 1 := by
      specialize h1 2
      norm_num at h1 ⊢
      linarith
    have h8 : (1 + f 1) * f 1 = 2 * f 1 := by
      simp [h6] at h4 h5
      nlinarith [h4, h5, h6]
    have h9 : f 1 = 0 ∨ f 1 = 1 := by
      by_cases h10 : f 1 > 0
      · -- f(1) > 0
        have h11 : f 1 = 1 := by
          nlinarith
        right
        exact h11
      · -- f(1) ≤ 0, so f(1) = 0
        have h12 : f 1 = 0 := by
          omega
        left
        exact h12
    cases h9 with
    | inl h10 =>
      -- f(1) = 0 so all f(n) = 0
      have h11 : ∀ n, f n = 0 := by
        intro n
        specialize h1 n
        simp [h10] at h1 ⊢
        <;> omega
      left
      funext n
      specialize h11 n
      simp [h11]
      <;> omega
    | inr h11 =>
      -- f(1) = 1 so all f(n) = n
      have h12 : ∀ n, f n = n := by
        intro n
        specialize h1 n
        simp [h11] at h1 ⊢
        <;> omega
      right
      funext n
      specialize h12 n
      simp [h12]
      <;> omega
  · -- Show that {0, id} satisfies the functional equation
    rintro (rfl | rfl)
    · -- Show that the zero function satisfies the equation
      intro m n
      all_goals simp
    · -- Show that the identity function satisfies the equation
      intro m n
      simp [mul_add, add_mul]
      <;> ring
      all_goals linarith