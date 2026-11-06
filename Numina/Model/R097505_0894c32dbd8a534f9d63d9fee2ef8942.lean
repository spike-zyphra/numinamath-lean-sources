import Mathlib

theorem number_theory_963 :
    {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ x ≤ y ∧ x ^ 2 + y ^ 2 = 2018}.encard = 1 := by
  have h1 : {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ x ≤ y ∧ x ^ 2 + y ^ 2 = 2018} = {(13, 43)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Forward direction: Show that if (x, y) satisfy all the conditions then (x, y) = (13, 43).
      rintro ⟨hx, hy, hxy, h_eq⟩
      have h2 : x ≤ 31 := by nlinarith
      have h3 : y ≤ 44 := by nlinarith
      interval_cases x <;> try { interval_cases y <;> omega }
    · -- Backward direction: Show that (13, 43) satisfies all the conditions.
      rintro ⟨rfl, rfl⟩
      all_goals
        native_decide
  rw [h1]
  simp [Set.encard]
  <;> try { native_decide }