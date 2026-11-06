import Mathlib
open Real Finset Set Complex

theorem algebra_604385 (a b c d : ℝ)
  (h : ∃ x y z t : ℝ,
      [x, y, z, t] ∈ List.permutations [a, b, c, d] ∧
      x ≤ 2 * a - b ∧ y ≤ 2 * b - c ∧ z ≤ 2 * c - d ∧ t ≤ 2 * d - a) :
  a = b ∧ b = c ∧ c = d := by
  obtain ⟨x, y, z, t, h_perm, h_x_ineq, h_y_ineq, h_z_ineq, h_t_ineq⟩ := h
  
  have h_sum_ineq : x + y + z + t ≤ a + b + c + d := by
    calc
      x + y + z + t ≤ (2 * a - b) + (2 * b - c) + (2 * c - d) + (2 * d - a) := by
        apply add_le_add
        · apply add_le_add
          · apply add_le_add
            · exact h_x_ineq
            · exact h_y_ineq
          · exact h_z_ineq
        · exact h_t_ineq
      _ = (2 * a - a) + (2 * b - b) + (2 * c - c) + (2 * d - d) := by
        ring
      _ = a + b + c + d := by
        simp [two_mul]
  
  have h_sum_eq : x + y + z + t = a + b + c + d := by
    have h_list_perm : List.Perm [x, y, z, t] [a, b, c, d] := by
      exact List.mem_permutations.mp h_perm
    have : List.sum [x, y, z, t] = List.sum [a, b, c, d] := by
      exact h_list_perm.sum_eq
    simp [List.sum] at this
    rw [← add_assoc,← add_assoc,← add_assoc,← add_assoc] at this
    exact this
  
  have h_eqs : x = 2 * a - b ∧ y = 2 * b - c ∧ z = 2 * c - d ∧ t = 2 * d - a := by
    have h_eq : x + y + z + t = (2 * a - b) + (2 * b - c) + (2 * c - d) + (2 * d - a) := by
      have h_sum_right : (2 * a - b) + (2 * b - c) + (2 * c - d) + (2 * d - a) = a + b + c + d := by
        ring
      rw [h_sum_right, h_sum_eq]
    have h_x_le : x ≤ 2 * a - b := h_x_ineq
    have h_y_le : y ≤ 2 * b - c := h_y_ineq
    have h_z_le : z ≤ 2 * c - d := h_z_ineq
    have h_t_le : t ≤ 2 * d - a := h_t_ineq
    have h_all_eq : x = 2 * a - b ∧ y = 2 * b - c ∧ z = 2 * c - d ∧ t = 2 * d - a := by
      apply And.intro
      · apply le_antisymm h_x_le
        have : x + y + z + t = (2 * a - b) + (2 * b - c) + (2 * c - d) + (2 * d - a) := h_eq
        linarith
      · apply And.intro
        · apply le_antisymm h_y_le
          have : x + y + z + t = (2 * a - b) + (2 * b - c) + (2 * c - d) + (2 * d - a) := h_eq
          linarith
        · apply And.intro
          · apply le_antisymm h_z_le
            have : x + y + z + t = (2 * a - b) + (2 * b - c) + (2 * c - d) + (2 * d - a) := h_eq
            linarith
          · apply le_antisymm h_t_le
            have : x + y + z + t = (2 * a - b) + (2 * b - c) + (2 * c - d) + (2 * d - a) := h_eq
            linarith
    exact h_all_eq
  
  have h_square_sum : a^2 + b^2 + c^2 + d^2 = (x^2 + y^2 + z^2 + t^2) := by
    have h_list_perm : List.Perm [x, y, z, t] [a, b, c, d] := by
      exact List.mem_permutations.mp h_perm
    have : List.sum ([x, y, z, t].map (fun x => x^2)) = List.sum ([a, b, c, d].map (fun x => x^2)) := by
      exact (List.Perm.map (fun x => x^2) h_list_perm).sum_eq
    -- Now we expand the map and sum
    simp [List.map, List.sum] at this
    rw [← add_assoc, ← add_assoc, ← add_assoc,← add_assoc] at this
    nlinarith
  
  have h_x_eq : x = 2 * a - b := h_eqs.1
  have h_y_eq : y = 2 * b - c := h_eqs.2.1
  have h_z_eq : z = 2 * c - d := h_eqs.2.2.1
  have h_t_eq : t = 2 * d - a := h_eqs.2.2.2
  rw [h_x_eq, h_y_eq, h_z_eq, h_t_eq] at h_square_sum
  -- Now we form individual equations
  ring_nf at h_square_sum
  have h1 : (a - b) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - d), sq_nonneg (d - a)]
  have h2 : (b - c) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - d), sq_nonneg (d - a)]
  have h3 : (c - d) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - d), sq_nonneg (d - a)]
  
  have h4 : a - b = 0 := by
    nlinarith [pow_eq_zero h1]
  have h5 : b - c = 0 := by
    nlinarith [pow_eq_zero h2]
  have h6 : c - d = 0 := by
    nlinarith [pow_eq_zero h3]
  
  constructor
  · -- a = b
    linarith [h4]
  constructor
  · -- b = c
    linarith [h5]
  · -- c = d
    linarith [h6]