import Mathlib

theorem inequalities_72227 : {f : ℝ → ℝ | ∀ x y, f (x ^ 2) - f (y ^ 2) ≤ (f x + y) * (x - f y)} = {id, -id} := by
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- Assume f satisfies the inequality, prove f = id or f = -id
    intro h
    have h1 : f 0 = 0 := by
      have h2 := h 0 0
      norm_num at h2
      nlinarith [sq_nonneg (f 0)]
    have h3 : ∀ y : ℝ, f (y ^ 2) ≥ y * f y := by
      intro y
      have h4 := h 0 y
      simp [h1] at h4
      nlinarith
    have h4 : ∀ x : ℝ, f (x ^ 2) ≤ x * f x := by
      intro x
      have h5 := h x 0
      simp [h1] at h5
      nlinarith
    have h5 : ∀ x : ℝ, f (x ^ 2) = x * f x := by
      intro x
      have h6 := h3 x
      have h7 := h4 x
      linarith
    have h6 : ∀ x : ℝ, f (-x) = -f x := by
      intro x
      have eq1 : f (x ^ 2) = x * f x := by
        apply h5 x
      have eq4 : f ((-x) ^ 2) = (-x) * f (-x) := by
        apply h5 (-x)
      have eq5 : (-x : ℝ) ^ 2 = x ^ 2 := by
        ring
      rw [eq5] at eq4
      have h6 : x * f x = (-x) * f (-x) := by linarith [eq1, eq4]
      have hx0 : x * f x = (-x) * f (-x) := h6
      by_cases h66 : x = 0
      · -- x = 0
        rw [h66]
        simp [h1]
      · -- x ≠ 0
        have hxne : x ≠ 0 := h66
        have eq7 : f x = -f (-x) := by
          apply (mul_left_inj' hxne).mp
          linarith
        have eq8 : f (-x) = -f x := by linarith [eq7]
        linarith [eq8]
    -- Show that f(x) f(y) = x y
    have h7 : ∀ x y : ℝ, f x * f y = x * y := by
      intro x y
      have h8 : f x * f y ≤ x * y := by
        have h9 := h x y
        have h10 : f (x ^ 2) = x * f x := h5 x
        have h11 : f (y ^ 2) = y * f y := h5 y
        nlinarith [sq_nonneg (x - y), sq_nonneg (f x - f y), sq_nonneg (f x - x), sq_nonneg (f y - y)]
      have h90 : f x * f y ≥ x * y := by
        have h9 := h x (-y)
        have h10 : f (x ^ 2) = x * f x := h5 x
        have h11 : f ((-y) ^ 2) = (-y) * f (-y) := h5 (-y)
        have h12 : (-y : ℝ) ^ 2 = y ^ 2 := by ring
        have h13 : f (y ^ 2) = y * f y := by
          have h14 : f (y ^ 2) = y * f y := h5 y
          linarith
        have h14 : f (-y) = -f y := h6 y
        have h30 : f (x ^ 2) - f (y ^ 2) ≤ (f x + (-y)) * (x - f (-y)) := by
          simpa using h9
        have h31 : f (x ^ 2) = x * f x := by
          apply h5 x
        have h32 : f ((-y) ^ 2) = -y * f (-y) := by
          apply h5 (-y)
        have h33 : (-y : ℝ) ^ 2 = y ^ 2 := by ring
        have h34 : f (-y) = -f y := h6 y
        have h35 : f ((-y) ^ 2) = -y * f (-y) := h32
        rw [h33] at h35
        rw [h34] at h35
        have h36 : f (x ^ 2) - f (y ^ 2) = x * f x - y * f y := by
          linarith [h31, h35]
        have h37 : (f x + (-y)) * (x - f (-y)) = (f x - y) * (x + f y) := by
          rw [show f (-y) = -f y by linarith [h34]]
          ring
        rw [h36, h37] at h30
        nlinarith
      linarith
    have h8 : f 1 = 1 ∨ f 1 = -1 := by
      have h9 : f 1 * f 1 = 1 * 1 := h7 1 1
      have h10 : f 1 ^ 2 = 1 := by
        nlinarith
      have h11 : f 1 = 1 ∨ f 1 = -1 := by
        rw [sq_eq_one_iff] at h10
        exact h10
      exact h11
    cases h8 with
    | inl h81 =>
      have h9 : ∀ x : ℝ, f x = x := by
        intro x
        have h10 := h7 x 1
        simp [h81] at h10
        nlinarith
      have h10 : f = id := by
        funext x
        exact h9 x
      left
      exact h10
    | inr h81 =>
      have h9 : ∀ x : ℝ, f x = -x := by
        intro x
        have h10 := h7 x 1
        simp [h81] at h10
        nlinarith
      have h10 : f = -id := by
        funext x
        exact h9 x
      right
      exact h10
  · -- Show that id and -id satisfy the inequality
    rintro (rfl | rfl)
    · -- Check f = id
      intro x y
      simp
      <;> nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]
    · -- Check f = -id
      intro x y
      simp
      <;> nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]