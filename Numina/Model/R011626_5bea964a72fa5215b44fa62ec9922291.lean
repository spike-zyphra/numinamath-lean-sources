import Mathlib

def f: ℝ → ℝ := fun x => min (x ^ 2 - 1) (min (x + 1) (-x + 1))

-- we simplify the function f by cases of range x
lemma f_eq_1: ∀ x, x ≤ -1 → f x = x + 1 := by  -- f x = x + 1 for x ≤ -1
  intro x h
  simp [f]
  have s: (x ^ 2 - 1) ⊓ ((x + 1) ⊓ (-x + 1)) = (x + 1) ⊓ (-x + 1) := by
    simp
    left
    nlinarith
  rw [s]
  clear s
  simp
  nlinarith

lemma f_eq_2: ∀ x, -1 ≤ x ∧ x ≤ 1 → f x = x ^ 2 - 1 := by  -- f x = x ^ 2 - 1 for -1 ≤ x ≤ 1
  intro x h
  simp [f]
  constructor
  .
    nlinarith
  .
    nlinarith

lemma f_eq_3: ∀ x, 1 ≤ x → f x = -x + 1 := by
  intro x h
  simp [f]
  have s: (x ^ 2 - 1) ⊓ ((x + 1) ⊓ (-x + 1)) = (x + 1) ⊓ (-x + 1) := by
    simp
    right
    nlinarith
  rw [s]
  clear s
  simp
  nlinarith

theorem algebra_190727: {a: ℝ | f (a + 2) > f a} = Set.Iio (-2) ∪ Set.Ioo (-1) 0 := by
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioo]
  by_cases h1 : a ≤ -1
  · -- Case a ≤ -1
    by_cases h2 : a + 2 ≤ -1
    · -- Case 1: a+2 ≤ -1, so a ≤ -3.
      have ha1 : f a = a + 1 := f_eq_1 a h1
      have ha2 : f (a + 2) = (a + 2) + 1 := by
        apply f_eq_1 (a + 2) h2
      rw [ha1, ha2]
      constructor
      · -- Assume a + 2 + 1 > a + 1
        intro h
        left
        nlinarith
      · -- Assume a < -2 ∨ ( -1 < a ∧ a < 0)
        rintro (h | ⟨h1, h2⟩)
        · -- Assume a < -2.
          linarith
        · -- Assume -1 < a ∧ a < 0, inconsistency with a ≤ -1.
          nlinarith
    · -- Case 2: a+2 > -1. So $a > -3$ and $a \le -1$. Hence $-3 < a \le -1$.
      have h4 : a > -3 := by linarith
      have ha1 : f a = a + 1 := f_eq_1 a h1
      have h5 : a + 2 ≤ 1 := by nlinarith
      have h6 : -1 < a + 2 := by nlinarith
      have ha2 : f (a + 2) = (a + 2) ^ 2 - 1 := by
        apply f_eq_2 (a + 2)
        constructor
        · -- Show -1 ≤ a + 2
          linarith
        · -- Show a + 2 ≤ 1
          linarith
      rw [ha1, ha2]
      constructor
      · -- Assume (a + 2)^2 - 1 > a + 1
        intro h
        by_cases h4 : a < -2
        · -- Assume a < -2.
          left
          linarith
        · -- Assume a ≥ -2. We have a ≤ -1.
          nlinarith [sq_nonneg (a + 1)]
      · -- Assume a < -2 ∨ ( -1 < a ∧ a < 0)
        rintro (h | ⟨h1, h2⟩)
        · -- Assume a < -2. This part.
          nlinarith
        · -- Assume -1 < a ∧ a < 0, inconsistency with a ≤ -1.
          nlinarith
  · -- Case a > -1
    have h2' : -1 < a := by linarith
    by_cases h11 : a ≤ 1
    · -- Case -1 < a ≤ 1.
      have ha1 : f a = a ^ 2 - 1 := by
        apply f_eq_2 a
        constructor
        · -- Show -1 ≤ a
          linarith
        · -- Show a ≤ 1
          linarith
      have ha2 : f (a + 2) = - (a + 2) + 1 := by
        have h5 : 1 ≤ a + 2 := by nlinarith
        apply f_eq_3 (a + 2) h5
      rw [ha1, ha2]
      constructor
      · -- Assume - (a + 2) + 1 > a ^ 2 - 1
        intro h
        have : -1 < a ∧ a < 0 := by
          constructor <;> nlinarith
        tauto
      · -- Assume (a < -2) ∨ ( -1 < a ∧ a < 0)
        rintro (h | ⟨h1, h2⟩)
        · -- Assume a < -2. Insignificant here.
          nlinarith
        · -- Assume -1 < a ∧ a < 0
          nlinarith
    · -- Case a > 1
      have ha1 : f a = -a + 1 := by
        have h5 : 1 ≤ a := by nlinarith
        apply f_eq_3 a h5
      have ha2 : f (a + 2) = - (a + 2) + 1 := by
        have h5 : 1 ≤ a + 2 := by nlinarith
        apply f_eq_3 (a + 2) h5
      rw [ha1, ha2]
      constructor
      · -- Assume - (a + 2) + 1 > -a + 1
        intro h
        nlinarith
      · -- Assume (a < -2) ∨ ( -1 < a ∧ a < 0)
        rintro (h | ⟨h1, h2⟩)
        · -- Assume a < -2.
          nlinarith
        · -- Assume -1 < a ∧ a < 0. Doesn't apply here.
          nlinarith