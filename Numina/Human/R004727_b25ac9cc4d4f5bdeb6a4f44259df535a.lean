import Mathlib

-- we show vieta's formula
lemma vieta_formula (p q x1 x2: ℝ) (ne: ¬x1 = x2) (h1: x1 ^ 2 + p * x1 + q = 0) (h2: x2 ^ 2 + p * x2 + q = 0):
    x1 + x2 = -p ∧ x1 * x2 = q := by

  have h: (x1 - x2) * (x1 + x2 + p) = 0 := by nlinarith
  replace ne: ¬ x1 - x2 = 0 := by
    by_contra! i
    replace i: x1 = x2 := by linarith
    simp [i] at ne
  simp [ne] at h
  constructor
  .
    linarith
  .
    have f: (x1 + x2) ^ 2 - 2 * (x1 * x2) + p * (x1 + x2) + 2 * q = 0 := by
      nlinarith
    replace h: x1 + x2 = -p := by linarith
    simp [h] at f
    nlinarith


/-If the three roots of the equation
(x−1)(x^2−2x+m)=0 can serve as the lengths of the three sides of a triangle,
then the range of the real number m is ( ).
(A) 0 < m ⩽ 1
(B) 3 / 4 ≤  m
(C) 3 / 4 < m ⩽ 1
(D) m ⩾ 1-/

theorem algebra_311554 {m x1 x2: ℝ} (l1: 0 < x1) (l2: 0 < x2) (h1: x1 ^ 2 - 2 * x1 + m = 0) (h2: x2 ^ 2 - 2 * x2 + m = 0)
  (h: ∀ y, y ^ 2 - 2 * y + m = 0 → y = x1 ∨ y = x2) (l: |x1 - x2| < 1): 3 / 4 < m ∧ m ≤ 1 := by

    by_cases r: x1 = x2

    -- case 1: multiple roots
    .
      simp [← r] at *
      clear l r h2 l2
      set y:= 2 - x1
      have f: y ^ 2 - 2 * y + m = 0 := by
        simp [y]
        nlinarith
      specialize h y f
      simp [y] at h
      replace h: x1 = 1 := by linarith
      simp [h] at h1
      replace h1: m = 1 := by linarith
      simp [h1]
      norm_num

    -- case 2: distinct roots, we apply vieta's lemma
    .
      have f:= vieta_formula (-2) m x1 x2 r (by nlinarith) (by nlinarith)
      rcases f with ⟨f, g⟩
      have s1: 0 < m := by rw [← g]; nlinarith
      simp at f
      have u: (x1 - x2) ^ 2 = 4 - 4 * m := by nlinarith

      -- we first show that m ≤ 1
      have s2: m ≤ 1 := by
        have v: 0 ≤ 4 - 4 * m := by
          rw [← u]
          nlinarith
        linarith
      simp [s2]

      -- for the rest, we show that 3 / 4 < m
      replace l: (x1 - x2) ^ 2 < 1 := by
        have i: (x1 - x2) ^ 2 = |x1 - x2| ^ 2 := by
          simp
        rw [i]
        set q:= |x1 - x2|
        have rq: 0 ≤ q := by
          simp [q]
        nlinarith
      simp [u] at l
      linarith