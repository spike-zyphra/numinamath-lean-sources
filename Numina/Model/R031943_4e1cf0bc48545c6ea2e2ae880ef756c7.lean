import Mathlib

theorem number_theory_52912 : {(w, x, y, z) : ℕ × ℕ × ℕ × ℕ | w > 0 ∧ x > 0 ∧ y > 0 ∧ z > 0 ∧ Nat.factorial w = Nat.factorial x + Nat.factorial y + Nat.factorial z} = {(3, 2, 2, 2)} := by
  ext ⟨w, x, y, z⟩
  simp [-Nat.factorial]
  constructor
  · -- Assume (w, x, y, z) in the set
    rintro ⟨hw, hx, hy, hz, h⟩
    by_cases h1 : w < 4
    · -- Then w = 1, 2, or 3
      have hw1 : w = 1 ∨ w = 2 ∨ w = 3 := by omega
      rcases hw1 with (hw1 | hw1 | hw1)
      · -- w = 1
        rw [hw1] at h
        have h1 : Nat.factorial 1 = Nat.factorial x + Nat.factorial y + Nat.factorial z := h
        simp [Nat.factorial] at h1
        have h2 : x ≥ 1 := by linarith
        have h3 : y ≥ 1 := by linarith
        have h4 : z ≥ 1 := by linarith
        have h5 : Nat.factorial x ≥ 1 := by
          apply Nat.factorial_pos
        have h6 : Nat.factorial y ≥ 1 := by
          apply Nat.factorial_pos
        have h7 : Nat.factorial z ≥ 1 := by
          apply Nat.factorial_pos
        omega
      · -- w = 2
        rw [hw1] at h
        have h2 : Nat.factorial 2 = Nat.factorial x + Nat.factorial y + Nat.factorial z := h
        simp [Nat.factorial] at h2
        have h21 : x ≥ 1 := by linarith
        have h22 : y ≥ 1 := by linarith
        have h23 : z ≥ 1 := by linarith
        have h5 : Nat.factorial x ≥ 1 := by
          apply Nat.factorial_pos
        have h6 : Nat.factorial y ≥ 1 := by
          apply Nat.factorial_pos
        have h7 : Nat.factorial z ≥ 1 := by
          apply Nat.factorial_pos
        omega
      · -- w = 3
        rw [hw1] at h
        have h3 : Nat.factorial 3 = Nat.factorial x + Nat.factorial y + Nat.factorial z := h
        simp [Nat.factorial] at h3
        have h21 : x ≤ 3 := by
          by_contra h21
          push_neg at h21
          have h22 : x ≥ 4 := by omega
          have h23 : Nat.factorial x ≥ 24 := by
            have h24 : x ≥ 4 := h22
            have h25 : Nat.factorial x ≥ Nat.factorial 4 := by
              apply Nat.factorial_le
              all_goals omega
            have h26 : Nat.factorial 4 = 24 := by
              simp [Nat.factorial]
            have h27 : Nat.factorial x ≥ 24 := by
              linarith
            linarith
          omega
        have h22 : y ≤ 3 := by
          by_contra h22
          push_neg at h22
          have h23 : y ≥ 4 := by omega
          have h24 : Nat.factorial y ≥ 24 := by
            have h25 : y ≥ 4 := h23
            have h26 : Nat.factorial y ≥ Nat.factorial 4 := by
              apply Nat.factorial_le
              all_goals omega
            have h27 : Nat.factorial 4 = 24 := by
              simp [Nat.factorial]
            have h28 : Nat.factorial y ≥ 24 := by
              linarith
            linarith
          omega
        have h23 : z ≤ 3 := by
          by_contra h23
          push_neg at h23
          have h24 : z ≥ 4 := by omega
          have h25 : Nat.factorial z ≥ 24 := by
            have h26 : z ≥ 4 := h24
            have h27 : Nat.factorial z ≥ Nat.factorial 4 := by
              apply Nat.factorial_le
              all_goals omega
            have h28 : Nat.factorial 4 = 24 := by
              simp [Nat.factorial]
            have h29 : Nat.factorial z ≥ 24 := by
              linarith
            linarith
          omega
        interval_cases x <;> interval_cases y <;> interval_cases z
        <;> simp [Nat.factorial] at h3 <;> tauto
    · -- w ≥ 4
      have h1 : w ≥ 4 := by omega
      have h2 : x < w := by
        by_contra h2
        push_neg at h2
        have h3 : x ≥ w := by omega
        have h4 : Nat.factorial x ≥ Nat.factorial w := by
          apply Nat.factorial_le
          all_goals
          omega
        have h5 : Nat.factorial x + Nat.factorial y + Nat.factorial z ≥ Nat.factorial w := by
          have h6 : Nat.factorial y ≥ 0 := by positivity
          have h7 : Nat.factorial z ≥ 0 := by positivity
          linarith
        nlinarith [Nat.factorial_pos w, Nat.factorial_pos x, Nat.factorial_pos y, Nat.factorial_pos z]
      have h3 : y < w := by
        by_contra h3
        push_neg at h3
        have h4 : y ≥ w := by omega
        have h5 : Nat.factorial y ≥ Nat.factorial w := by
          apply Nat.factorial_le
          all_goals
          omega
        have h6 : Nat.factorial x + Nat.factorial y + Nat.factorial z ≥ Nat.factorial w := by
          have h7 : Nat.factorial x ≥ 0 := by positivity
          have h8 : Nat.factorial z ≥ 0 := by positivity
          linarith
        nlinarith [Nat.factorial_pos w, Nat.factorial_pos x, Nat.factorial_pos y, Nat.factorial_pos z]
      have h4 : z < w := by
        by_contra h4
        push_neg at h4
        have h5 : z ≥ w := by omega
        have h6 : Nat.factorial z ≥ Nat.factorial w := by
          apply Nat.factorial_le
          all_goals
          omega
        have h7 : Nat.factorial x + Nat.factorial y + Nat.factorial z ≥ Nat.factorial w := by
          have h8 : Nat.factorial x ≥ 0 := by positivity
          have h9 : Nat.factorial y ≥ 0 := by positivity
          linarith
        nlinarith [Nat.factorial_pos w, Nat.factorial_pos x, Nat.factorial_pos y, Nat.factorial_pos z]
      have h5 : Nat.factorial w > 3 * Nat.factorial (w - 1) := by
        have hw8 : w ≥ 4 := by omega
        have h7 : Nat.factorial w = w * Nat.factorial (w - 1) := by
          cases w with
          | zero => linarith
          | succ n => 
            simp [Nat.factorial] at *
            <;> omega
        rw [h7]
        have hw9 : w > 3 := by omega
        have hw10 : Nat.factorial (w - 1) > 0 := by positivity
        nlinarith
      have h6 : Nat.factorial x + Nat.factorial y + Nat.factorial z ≤ 3 * Nat.factorial (w - 1) := by
        have hx7 : x ≤ w - 1 := by omega
        have hy7 : y ≤ w - 1 := by omega
        have hz7 : z ≤ w - 1 := by omega
        have h7 : Nat.factorial x ≤ Nat.factorial (w - 1) := by
          apply Nat.factorial_le
          all_goals
          omega
        have h8 : Nat.factorial y ≤ Nat.factorial (w - 1) := by
          apply Nat.factorial_le
          all_goals
          omega
        have h9 : Nat.factorial z ≤ Nat.factorial (w - 1) := by
          apply Nat.factorial_le
          all_goals
          omega
        linarith
      nlinarith [Nat.factorial_pos w, Nat.factorial_pos x, Nat.factorial_pos y, Nat.factorial_pos z]
  · -- Show that (3, 2, 2, 2) is in the set
    rintro ⟨rfl, rfl, rfl, rfl⟩
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    all_goals norm_num [Nat.factorial]