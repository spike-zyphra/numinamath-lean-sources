import Mathlib

theorem algebra_268503 : {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ (x / 4 : ℚ) = 9 / y}.encard = 9 := by
  have h1 : {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ (x / 4 : ℚ) = 9 / y} = Finset.filter (fun p => (p.1 > 0 ∧ p.2 > 0 ∧ (p.1 / 4 : ℚ) = 9 / p.2)) (Finset.Icc (0 : ℕ) 36 ×ˢ Finset.Icc (0 : ℕ) 36) := by
    ext ⟨x, y⟩
    simp
    intro hx hy h
    have h2 : (x : ℚ) / 4 = (9 : ℚ) / (y : ℚ) := by
      simpa using h
    have h3 : (x : ℚ) * (y : ℚ) = 36 := by
      field_simp at h2
      nlinarith
    have h4 : (x : ℕ) * (y : ℕ) = 36 := by
      exact_mod_cast h3
    have h5 : x ≤ 36 := by
      have h6 : x ∣ 36 := by
        use y
        all_goals linarith
      have h7 : x ≤ 36 := by
        apply Nat.le_of_dvd (by norm_num) h6
      linarith
    have h8 : y ≤ 36 := by
      have h9 : y ∣ 36 := by
        use x
        all_goals linarith
      have h10 : y ≤ 36 := by
        apply Nat.le_of_dvd (by norm_num) h9
      linarith
    omega
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide