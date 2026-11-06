import Mathlib

theorem number_theory_7433 :
    {(x, y) : ℤ × ℤ | abs x + 1 ≠ 0 ∧ abs y - 3 ≠ 0 ∧ (abs x + 1) * (abs y - 3) = 5}.ncard = 6 := by
  have h1 : {(x, y) : ℤ × ℤ | abs x + 1 ≠ 0 ∧ abs y - 3 ≠ 0 ∧ (abs x + 1) * (abs y - 3) = 5} = {(0, 8), (0, -8), (4, 4), (4, -4), (-4, 4), (-4, -4)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Assume (x,y) is in the left side, prove it is in the right side.
      rintro ⟨h1, h2, heq⟩
      have h3 : (abs x + 1) ∣ 5 := by
        use abs y - 3
        all_goals nlinarith
      have h4 : (abs x + 1) = 1 ∨ (abs x + 1) = 5 ∨ (abs x + 1) = -1 ∨ (abs x + 1) = -5 := by
        have h1 : (abs x + 1) ∣ 5 := h3
        have h5 : (abs x + 1) ≤ 5 := by
          apply Int.le_of_dvd (by norm_num) h1
        have h6 : (abs x + 1) ≥ -5 := by
          have h7 : abs x ≥ 0 := abs_nonneg x
          omega
        interval_cases (abs x + 1) <;> tauto
      rcases h4 with (h | h | h | h)
      · -- abs x + 1 = 1.
        have h5 : abs x = 0 := by
          omega
        have hx : x = 0 := by
          cases' abs_cases x with hx1 hx1
          all_goals omega
        have h6 : abs y - 3 = 5 := by
          rw [h] at heq
          linarith
        have h7 : abs y = 8 := by
          omega
        have hy : y = 8 ∨ y = -8 := by
          cases' abs_cases y with hy1 hy1
          all_goals omega
        rcases hy with (hy | hy)
        · -- y = 8
          simp [hx, hy]
        · -- y = -8
          simp [hx, hy]
      · -- abs x + 1 = 5
        have h5 : abs x = 4 := by
          omega
        have hx : x = 4 ∨ x = -4 := by
          cases' abs_cases x with hx1 hx1
          all_goals omega
        have h6 : abs y - 3 = 1 := by
          rw [h] at heq
          linarith
        have h7 : abs y = 4 := by
          omega
        have hy : y = 4 ∨ y = -4 := by
          cases' abs_cases y with hy1 hy1
          all_goals omega
        rcases hx with (hx | hx)
        all_goals
          rcases hy with (hy | hy)
          all_goals
            simp [hx, hy]
      · -- abs x + 1 = -1
        exfalso
        have h5 : abs x = -2 := by
          omega
        have h6 : abs x ≥ 0 := abs_nonneg x
        omega
      · -- abs x + 1 = -5
        exfalso
        have h5 : abs x = -6 := by
          omega
        have h6 : abs x ≥ 0 := abs_nonneg x
        omega
    · -- Assume (x,y) is in the right side, prove it is in the left side.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- (0,8)
        constructor
        · -- abs x + 1 ≠ 0
          norm_num
        constructor
        · -- abs y - 3 ≠ 0
          norm_num
        · -- (abs x + 1) * (abs y - 3) = 5
          norm_num
      · -- (0,-8)
        constructor
        · -- abs x + 1 ≠ 0
          norm_num
        constructor
        · -- abs y - 3 ≠ 0
          norm_num
        · -- (abs x + 1) * (abs y - 3) = 5
          norm_num
      · -- (4,4)
        constructor
        · -- abs x + 1 ≠ 0
          norm_num
        constructor
        · -- abs y - 3 ≠ 0
          norm_num
        · -- (abs x + 1) * (abs y - 3) = 5
          norm_num
      · -- (4,-4)
        constructor
        · -- abs x + 1 ≠ 0
          norm_num
        constructor
        · -- abs y - 3 ≠ 0
          norm_num
        · -- (abs x + 1) * (abs y - 3) = 5
          norm_num
      · -- (-4,4)
        constructor
        · -- abs x + 1 ≠ 0
          norm_num
        constructor
        · -- abs y - 3 ≠ 0
          norm_num
        · -- (abs x + 1) * (abs y - 3) = 5
          norm_num
      · -- (-4,-4)
        constructor
        · -- abs x + 1 ≠ 0
          norm_num
        constructor
        · -- abs y - 3 ≠ 0
          norm_num
        · -- (abs x + 1) * (abs y - 3) = 5
          norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }