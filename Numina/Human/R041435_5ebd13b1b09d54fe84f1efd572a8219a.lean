import Mathlib

/-Find all triplets of strictly positive integers $(x, y, z)$ with

$x \leq y \leq z$, such that $\frac{1}{x}+\frac{1}{y}+\frac{1}{z}=1$-/

theorem number_theory_295813 (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x ≤ y) (hyz : y ≤ z) :
    (1 / x : ℚ) + (1 / y : ℚ) + (1 / z : ℚ) = 1 ↔
    (x = 3 ∧ y = 3 ∧ z = 3) ∨ (x = 2 ∧ y = 4 ∧ z = 4) ∨ (x = 2 ∧ y = 3 ∧ z = 6) := by

  constructor
  · -- Forward direction: if (1/x + 1/y + 1/z = 1) then ((x = 3 ∧ y = 3 ∧ z = 3) ∨ (x = 2 ∧ y = 4 ∧ z = 4) ∨ (x = 2 ∧ y = 3 ∧ z = 6))
    intro h
    have h1 : x ≤ 3 := by
      by_contra hx'
      push_neg at hx'
      have h2 : (1 / x : ℚ) ≤ (1 / 4 : ℚ) := by
        have h3 : x ≥ 4 := by linarith
        have h4 : (x : ℚ) ≥ (4 : ℚ) := by exact_mod_cast h3
        have h5 : (1 / x : ℚ) ≤ (1 / 4 : ℚ) := by
          apply one_div_le_one_div_of_le
          all_goals linarith
        exact h5
      have h2' : (1 / y : ℚ) ≤ (1 / 4 : ℚ) := by
        have h3 : y ≥ 4 := by linarith [hxy, hx']
        have h4 : (y : ℚ) ≥ (4 : ℚ) := by exact_mod_cast h3
        have h5 : (1 / y : ℚ) ≤ (1 / 4 : ℚ) := by
          apply one_div_le_one_div_of_le
          all_goals linarith
        exact h5
      have h2'' : (1 / z : ℚ) ≤ (1 / 4 : ℚ) := by
        have h3 : z ≥ 4 := by linarith [hyz, hxy, hx']
        have h4 : (z : ℚ) ≥ (4 : ℚ) := by exact_mod_cast h3
        have h5 : (1 / z : ℚ) ≤ (1 / 4 : ℚ) := by
          apply one_div_le_one_div_of_le
          all_goals linarith
        exact h5
      have h3 : (1 / x : ℚ) + (1 / y : ℚ) + (1 / z : ℚ) ≤ (3 / 4 : ℚ) := by
        linarith
      linarith
    have h2 : x ≥ 2 := by
      by_contra hx'
      push_neg at hx'
      have h3 : x = 1 := by omega
      rw [h3] at h
      have h4 : (1 / (y : ℚ)) + (1 / (z : ℚ)) = (0 : ℚ) := by
        norm_num at h ⊢
        linarith
      have h5 : (1 / (y : ℚ)) + (1 / (z : ℚ)) > (0 : ℚ) := by
        have h6 : (y : ℚ) > (0 : ℚ) := by exact_mod_cast hy
        have h7 : (1 / (y : ℚ)) > (0 : ℚ) := by
          apply one_div_pos.mpr
          exact h6
        have h8 : (z : ℚ) > (0 : ℚ) := by exact_mod_cast hz
        have h9 : (1 / (z : ℚ)) > (0 : ℚ) := by
          apply one_div_pos.mpr
          exact h8
        linarith
      linarith
    interval_cases x <;> 
    try { 
      simp at h 
      <;> try omega 
    }
    · -- x = 2
      have h2 : y ≤ 4 := by
        by_contra hy'
        push_neg at hy'
        have h3 : y ≥ 5 := by omega
        have h4 : (1 / y : ℚ) ≤ (1 / 5 : ℚ) := by
          have h5 : y ≥ 5 := by linarith
          have h6 : (y : ℚ) ≥ (5 : ℚ) := by exact_mod_cast h5
          have h7 : (1 / y : ℚ) ≤ (1 / 5 : ℚ) := by
            apply one_div_le_one_div_of_le
            all_goals linarith
          exact h7
        have h5 : (1 / z : ℚ) ≤ (1 / 5 : ℚ) := by
          have h6 : z ≥ 5 := by linarith [hyz, h3]
          have h7 : (z : ℚ) ≥ (5 : ℚ) := by exact_mod_cast h6
          have h8 : (1 / z : ℚ) ≤ (1 / 5 : ℚ) := by
            apply one_div_le_one_div_of_le
            all_goals linarith
          exact h8
        have h6 : (1 / y : ℚ) + (1 / z : ℚ) < (1 / 2 : ℚ) := by
          linarith
        have h7 : (1 / (2 : ℕ) : ℚ) + (1 / y : ℚ) + (1 / z : ℚ) = 1 := by
          norm_num at h ⊢
          linarith
        norm_num at h7
        linarith
      interval_cases y <;> 
      try { 
        simp at h 
        <;> try omega 
      }
      · -- y = 2, leads to contradiction
        exfalso
        norm_num at h 
        all_goals linarith
      · -- y = 3
        have h3 : z = 6 := by
          field_simp at h
          norm_num at h
          have h4 : (z : ℚ) = (6 : ℚ) := by linarith
          exact_mod_cast h4
        right
        right
        exact ⟨by omega, by omega, by omega⟩
      · -- y = 4
        have h3 : z = 4 := by
          field_simp at h
          norm_num at h
          have h4 : (z : ℚ) = (4 : ℚ) := by linarith
          exact_mod_cast h4
        right
        left
        exact ⟨by omega, by omega, by omega⟩
    · -- x = 3
      have h2 : y ≤ 3 := by
        by_contra hy'
        push_neg at hy'
        have h3 : y ≥ 4 := by omega
        have h4 : (1 / y : ℚ) ≤ (1 / 4 : ℚ) := by
          have h5 : y ≥ 4 := by linarith
          have h6 : (y : ℚ) ≥ (4 : ℚ) := by exact_mod_cast h5
          have h7 : (1 / y : ℚ) ≤ (1 / 4 : ℚ) := by
            apply one_div_le_one_div_of_le
            all_goals linarith
          exact h7
        have h5 : (1 / z : ℚ) ≤ (1 / 4 : ℚ) := by
          have h6 : z ≥ 4 := by linarith [hyz, h3]
          have h7 : (z : ℚ) ≥ (4 : ℚ) := by exact_mod_cast h6
          have h8 : (1 / z : ℚ) ≤ (1 / 4 : ℚ) := by
            apply one_div_le_one_div_of_le
            all_goals linarith
          exact h8
        have h6 : (1 / y : ℚ) + (1 / z : ℚ) < (2 / 3 : ℚ) := by
          linarith
        have h7 : (1 / (3 : ℕ) : ℚ) + (1 / y : ℚ) + (1 / z : ℚ) = 1 := by
          norm_num at h ⊢
          linarith
        norm_num at h7
        linarith
      have h3 : y = 3 := by omega
      rw [h3] at h
      have h4 : z = 3 := by
        field_simp at h
        norm_num at h
        have h5 : (z : ℚ) = (3 : ℚ) := by linarith
        exact_mod_cast h5
      left
      exact ⟨by omega, by omega, by omega⟩
  · -- Reverse direction: if ((x = 3 ∧ y = 3 ∧ z = 3) ∨ (x = 2 ∧ y = 4 ∧ z = 4) ∨ (x = 2 ∧ y = 3 ∧ z = 6)) then (1/x + 1/y + 1/z = 1)
    rintro (h | h | h)
    · -- Case (3, 3, 3)
      rcases h with ⟨hx, hy, hz⟩
      rw [hx, hy, hz]
      norm_num
    · -- Case (2, 4, 4)
      rcases h with ⟨hx, hy, hz⟩
      rw [hx, hy, hz]
      norm_num
    · -- Case (2, 3, 6)
      rcases h with ⟨hx, hy, hz⟩
      rw [hx, hy, hz]
      norm_num