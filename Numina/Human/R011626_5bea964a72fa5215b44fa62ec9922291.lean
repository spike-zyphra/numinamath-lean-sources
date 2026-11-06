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

/-Let the function
f(x) = min{x ^ 2 - 1, x + 1, -x + 1},
if f(a + 2) > f a, then the range of real number a is-/

theorem algebra_190727: {a: ℝ | f (a + 2) > f a} = Set.Iio (-2) ∪ Set.Ioo (-1) 0 := by

  ext a
  constructor

  -- the forward direction
  .
    intro h
    simp only [Set.mem_setOf_eq] at h

    -- for convenience, we prove by contradiction
    by_contra! l
    simp at l
    absurd h
    simp
    clear h
    rcases l with ⟨l1, l2⟩
    by_cases l3: a ≤ -1

    -- case 1: a ≤ -1
    .
      clear l2
      have o: -1 ≤ a + 2 ∧ a + 2 ≤ 1 := by
        constructor
        .
          linarith
        .
          linarith
      have u:= f_eq_2 (a + 2) o
      rw [u]
      clear o u
      have v:= f_eq_1 a (by linarith)
      rw [v]
      clear v
      nlinarith

    -- case 2: 0 ≤ a
    .
      simp at l3
      simp [l3] at l2
      have u:= f_eq_3 (a + 2) (by linarith)
      rw [u]
      clear u
      clear l3 l1
      by_cases r: a ≤ 1
      -- case 2.1: a ≤ 1
      .
        have o: -1 ≤ a ∧ a ≤ 1 := by
          constructor
          .
            linarith
          .
            linarith
        have v:= f_eq_2 a o
        rw [v]
        clear o v
        nlinarith
      -- case 2.2: 1 ≤ a
      .
        simp at r
        clear l2
        have v:= f_eq_3 a (by linarith)
        rw [v]
        clear v
        nlinarith


  -- the backward direction
  .
    intro h
    simp at h
    rcases h with h | h

    -- case 1: a < -2
    .
      simp
      have u:= f_eq_1 a (by linarith)
      rw [u]
      clear u
      by_cases r: a ≤ -3
      -- case 1.1: a ≤ -3
      .
        have v:= f_eq_1 (a + 2) (by linarith)
        rw [v]
        clear v
        nlinarith
      -- case 1.2: -3 < a < -2
      .
        simp at r
        have o: -1 ≤ (a + 2) ∧ (a + 2) ≤ 1 := by
          constructor
          .
            linarith
          .
            linarith
        have v:= f_eq_2 (a + 2) o
        nlinarith

    -- case 2: -1 < a < 0
    .
      rcases h with ⟨l1, l2⟩
      simp
      have o: -1 ≤ a ∧ a ≤ 1 := by
        constructor
        .
          linarith
        .
          linarith
      have u:= f_eq_2 a o
      rw [u]
      clear u
      clear o
      have v:= f_eq_3 (a + 2) (by linarith)
      rw [v]
      clear v
      nlinarith