import Mathlib

theorem algebra_141443 :
    {(x, y, z) : ℕ × ℕ × ℕ | x > 0 ∧ y > 0 ∧ z > 0 ∧ x * y + y * z = 63 ∧ x * z + y * z = 23}.ncard = 2 := by
  have h1 : {(x, y, z) : ℕ × ℕ × ℕ | x > 0 ∧ y > 0 ∧ z > 0 ∧ x * y + y * z = 63 ∧ x * z + y * z = 23} = {(20, 3, 1), (2, 21, 1)} := by
    ext ⟨x, y, z⟩
    simp
    constructor
    · -- Assume ⟨x, y, z⟩ satisfy the system. Show ⟨x, y, z⟩ ∈ {(20, 3, 1), (2, 21, 1)}.
      rintro ⟨hx, hy, hz, h1, h2⟩
      have h3 : z ∣ 23 := by
        use x + y
        linarith
      have h4 : z = 1 ∨ z = 23 := by
        have : z ≤ 23 := by
          exact Nat.le_of_dvd (by norm_num) h3
        interval_cases z <;> tauto
      rcases h4 with (hz1 | hz23)
      · -- z = 1
        have h5 : x + y = 23 := by
          rw [hz1] at h2
          nlinarith
        have h6 : x * y + y * 1 = 63 := by
          rw [hz1] at h1
          linarith
        have h7 : y = 3 ∨ y = 21 := by
          have h8 : x = 23 - y := by
            omega
          rw [h8] at h6
          have h9 : y ≤ 23 := by
            omega
          interval_cases y <;> omega
        rcases h7 with (hy3 | hy21)
        · -- y = 3
          have hx20 : x = 20 := by
            omega
          simp [hx20, hy3, hz1]
          all_goals tauto
        · -- y = 21
          have hx2 : x = 2 := by
            omega
          simp [hx2, hy21, hz1]
          all_goals tauto
      · -- z = 23
        -- then x + y = 1 (from $z(x + y) = 23$), which is impossible
        -- since $x > 0$ and $y > 0$ implies $x + y ≥ 2$
        have h7 : x + y = 1 := by
          rw [hz23] at h2
          nlinarith
        have h8 : x ≥ 1 := by
          omega
        have h9 : y ≥ 1 := by
          omega
        omega
    · -- Now the reverse: both given triples satisfy the system
      rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
      · -- Check (20, 3, 1)
        constructor
        · norm_num -- x > 0
        constructor
        · norm_num -- y > 0
        constructor
        · norm_num -- z > 0
        constructor
        · norm_num -- x * y + y * z = 63
        · norm_num -- x * z + y * z = 23
      · -- Check (2, 21, 1)
        constructor
        · norm_num -- x > 0
        constructor
        · norm_num -- y > 0
        constructor
        · norm_num -- z > 0
        constructor
        · norm_num -- x * y + y * z = 63
        · norm_num -- x * z + y * z = 23
  rw [h1]
  rw [Set.ncard_pair]
  all_goals norm_num