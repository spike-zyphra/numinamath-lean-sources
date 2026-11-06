import Mathlib

theorem algebra_207790 {n : ℕ} (hn : n ≥ 4) (a : Fin n → ℝ)
    (ha : ∀ i j, i ≠ j → a i ≠ a j) (h : ∃ i j k l, i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l ∧
    (a i + a j) / 2 = (a i + a j + a k) / 3 ∧ (a i + a j + a k) / 3 = (a i + a j + a k + a l) / 4) :
    n = 5 := by

  rcases h with ⟨i, j, k, l, hine, hine2, hine3, hine4, hine5, hine6, h1, h2⟩

  have eq1 : a i + a j = 2 * a k := by
    linarith

  have eq2 : a i + a j + a k = 3 * a l := by
    linarith

  have eq3 : a k = a l := by
    linarith [eq1, eq2]

  have hne : k ≠ l := hine6

  have h3 : a k ≠ a l := by
    apply ha k l hne

  contradiction