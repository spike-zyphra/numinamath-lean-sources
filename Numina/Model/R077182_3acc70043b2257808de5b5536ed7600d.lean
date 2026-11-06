import Mathlib

theorem algebra_247 :
    {(x, y, z) : ℤ × ℤ × ℤ | x > 0 ∧ y > 0 ∧ z > 0 ∧ x * y + y * z = 63 ∧ x * z + y * z = 23}.ncard = 2 := by
  have h1 : {(x, y, z) : ℤ × ℤ × ℤ | x > 0 ∧ y > 0 ∧ z > 0 ∧ x * y + y * z = 63 ∧ x * z + y * z = 23} = {(2, 21, 1), (20, 3, 1)} := by
    ext ⟨x, y, z⟩
    simp
    constructor
    · rintro ⟨hx, hy, hz, heq⟩
      rcases heq with ⟨h1, h2⟩
      have h3 : z ∣ 23 := by
        use x + y
        linarith
      have h4 : z = 1 ∨ z = 23 := by
        have h23 : z ∣ 23 := h3
        have h5 : z ≤ 23 := by
          apply Int.le_of_dvd (by norm_num) h23
        have h6 : z ≥ 1 := by linarith
        interval_cases z <;> try { tauto }
      rcases h4 with (hz | hz)
      · -- Case z = 1 
        have h7 : x + y = 23 := by 
          rw [hz] at h2 
          linarith 
        have h8 : y * (x + 1) = 63 := by 
          rw [hz] at h1 
          nlinarith 
        have h9 : y = 21 ∨ y = 3 := by 
          have : y ≤ 63 := by 
            nlinarith 
          have : y ≥ 1 := hy 
          interval_cases y <;> omega 
        rcases h9 with (hy | hy)
        · -- Then from $x + y = 23$, we get $x = 2$ 
          have hx : x = 2 := by 
            linarith 
          simp [hx, hy, hz]
        · -- Then from $x + y = 23$, we get $x = 20$ 
          have hx : x = 20 := by 
            linarith 
          simp [hx, hy, hz]
      · -- Case $z = 23$ 
        rw [hz] at h1 h2 
        have h3 : x + y = 1 := by 
          linarith 
        -- Since $x + y = 1$ with $x > 0$ and $y > 0$ is a contradiction 
        have h4 : x > 0 := by assumption 
        have h5 : y > 0 := by assumption 
        linarith 
    · -- Show that both elements satisfy the equations 
      rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
      all_goals 
        norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> native_decide