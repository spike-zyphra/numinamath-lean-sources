import Mathlib

theorem number_theory_7242 (x y : ℕ) (hx : x > 0) (hy : y > 0) :
    3^x + 4^y = 5^2 ↔ x = 2 ∧ y = 2 := by
  constructor
  · -- Forward direction: If 3^x + 4^y = 25 with x > 0 and y > 0, then (x, y) = (2, 2)
    intro h
    have eq1 : 3^x + 4^y = 25 := by
      norm_num at h ⊢
      linarith
    have h1 : x ≤ 3 := by
      by_contra h2
      push_neg at h2
      have h2' : 3 ^ x ≥ 81 := by
        have h3 : x ≥ 4 := by linarith
        have h4 : 3 ^ x ≥ 3 ^ 4 := by
          apply Nat.pow_le_pow_of_le_right
          all_goals omega
        norm_num at h4 ⊢
        linarith
      have h3 : 4 ^ y ≥ 1 := by
        apply Nat.one_le_pow
        omega
      linarith [h2', h3, eq1]
    have h2 : y ≤ 3 := by
      by_contra h3
      push_neg at h3
      have h4 : 4 ^ y ≥ 256 := by
        have h5 : y ≥ 4 := by linarith
        have h6 : 4 ^ y ≥ 4 ^ 4 := by
          apply Nat.pow_le_pow_of_le_right
          all_goals omega
        norm_num at h6 ⊢
        linarith
      have h7 : 3 ^ x ≥ 1 := by
        apply Nat.one_le_pow
        omega
      linarith [h4, h7, eq1]
    interval_cases x <;> interval_cases y
    <;> norm_num at eq1 ⊢
    <;> tauto
  · -- Backward direction: If (x, y) = (2, 2), then 3^x + 4^y = 25
    rintro ⟨rfl, rfl⟩
    norm_num