import Mathlib

theorem algebra_196892 {n : ℕ} (hn : n ≥ 4) (a : Fin n → ℝ)
    (ha : ∀ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k → a i ≠ a j ∧ a i ≠ a k ∧ a j ≠ a k)
    (h : ∃ i j k l, i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l ∧
      (a i + a j) / 2 = (a i + a j + a k) / 3 ∧
      (a i + a j + a k) / 3 = (a i + a j + a k + a l) / 4) :
    n = 5 := by
  rcases h with ⟨i, j, k, l, h1, h2, h3, h4, h5, h6, h7, h8⟩
  -- Derive that a k = a l from the given equations
  have h9 : a k = a l := by
    linarith
  -- Derive a contradiction because a k should not equal a l
  have h11' : a k ≠ a l := by
    have h12 : i ≠ k ∧ i ≠ l ∧ k ≠ l := by
      tauto
    have h13 : a i ≠ a k ∧ a i ≠ a l ∧ a k ≠ a l := by 
      apply ha 
      exact h12
    tauto
  -- Final contradiction
  contradiction