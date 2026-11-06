import Mathlib
open Real Finset Set Complex

/- Soit $a, b, c$ et $d$ quatre nombres réels. On suppose qu'il existe une permutation $(x, y, z, t)$ des nombres $a, b, c$ et $d$ telle que
$$
x \leqslant 2 a-b, y \leqslant 2 b-c, z \leqslant 2 c-d \text { et } t \leqslant 2 d-a .
$$
Démontrer que $a=b=c=d$. -/
theorem algebra_604385 (a b c d : ℝ)
  (h : ∃ x y z t : ℝ,
      [x, y, z, t] ∈ List.permutations [a, b, c, d] ∧
      x ≤ 2 * a - b ∧ y ≤ 2 * b - c ∧ z ≤ 2 * c - d ∧ t ≤ 2 * d - a) :
  a = b ∧ b = c ∧ c = d := by
  -- Step $1$: Obtain the permutation $(x, y, z, t)$ satisfying the conditions.
  obtain ⟨x, y, z, t, h_perm, h_x_ineq, h_y_ineq, h_z_ineq, h_t_ineq⟩ := h
  -- Step $2$: Sum the four inequalities to obtain $x + y + z + t ≤ a + b + c + d$.
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
  -- Step $3$: Since $[x, y, z, t] ∈ List.permutations [a, b, c, d]$, $x + y + z + t = a + b + c + d$.
  have h_sum_eq : x + y + z + t = a + b + c + d := by
    have h_list_perm : List.Perm [x, y, z, t] [a, b, c, d] := by
      exact List.mem_permutations.mp h_perm
    have : List.sum [x, y, z, t] = List.sum [a, b, c, d] := by
      exact h_list_perm.sum_eq
    simp [List.sum] at this
    rw [← add_assoc,← add_assoc,← add_assoc,← add_assoc] at this
    exact this
  -- Step $4$: Therefore, the four inequalities are equalities.
  have h_eqs : x = 2 * a - b ∧ y = 2 * b - c ∧ z = 2 * c - d ∧ t = 2 * d - a := by
    have h_eq : x + y + z + t = (2 * a - b) + (2 * b - c) + (2 * c - d) + (2 * d - a) := by
      have h_sum_right : (2 * a - b) + (2 * b - c) + (2 * c - d) + (2 * d - a) = a + b + c + d := by
        ring
      rw [h_sum_right, h_sum_eq]
    have h_x_le : x ≤ 2 * a - b := h_x_ineq
    have h_y_le : y ≤ 2 * b - c := h_y_ineq
    have h_z_le : z ≤ 2 * c - d := h_z_ineq
    have h_t_le : t ≤ 2 * d - a := h_t_ineq
    have h_sum_le : x + y + z + t ≤ (2 * a - b) + (2 * b - c) + (2 * c - d) + (2 * d - a) := by
      apply add_le_add
      · apply add_le_add
        · apply add_le_add
          · exact h_x_le
          · exact h_y_le
        · exact h_z_le
      · exact h_t_le
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
  -- Step $5$: Square and sum to obtain $a^2 + b^2 + c^2 + d^2 = 5(a^2 + b^2 + c^2 + d^2) - 4(ab + bc + cd + da)$.
  have h_square_sum : a^2 + b^2 + c^2 + d^2 = 5 * (a^2 + b^2 + c^2 + d^2) - 4 * (a * b + b * c + c * d + d * a) := by
    have h_x_eq : x = 2 * a - b := h_eqs.1
    have h_y_eq : y = 2 * b - c := h_eqs.2.1
    have h_z_eq : z = 2 * c - d := h_eqs.2.2.1
    have h_t_eq : t = 2 * d - a := h_eqs.2.2.2
    have h_left : x^2 + y^2 + z^2 + t^2 = a^2 + b^2 + c^2 + d^2 := by
      have h_list_perm : List.Perm [x, y, z, t] [a, b, c, d] := by
        exact List.mem_permutations.mp h_perm
      have : List.sum ([x, y, z, t].map (fun x => x^2)) = List.sum ([a, b, c, d].map (fun x => x^2)) := by
        exact (List.Perm.map (fun x => x^2) h_list_perm).sum_eq
      simp [List.map, List.sum] at this
      rw [← add_assoc, ← add_assoc, ← add_assoc,← add_assoc] at this
      exact this
    have h_right : x^2 + y^2 + z^2 + t^2 = (2 * a - b)^2 + (2 * b - c)^2 + (2 * c - d)^2 + (2 * d - a)^2 := by
      rw [h_x_eq, h_y_eq, h_z_eq, h_t_eq]
    have h_right_expand : (2 * a - b)^2 + (2 * b - c)^2 + (2 * c - d)^2 + (2 * d - a)^2 =
                         5 * (a^2 + b^2 + c^2 + d^2) - 4 * (a * b + b * c + c * d + d * a) := by
      calc
        (2 * a - b)^2 + (2 * b - c)^2 + (2 * c - d)^2 + (2 * d - a)^2
        = (4 * a^2 - 4 * a * b + b^2) + (4 * b^2 - 4 * b * c + c^2) +
          (4 * c^2 - 4 * c * d + d^2) + (4 * d^2 - 4 * d * a + a^2) := by
          rw [sq, sq, sq, sq]
          ring
        _ = 5 * a^2 + 5 * b^2 + 5 * c^2 + 5 * d^2 - 4 * a * b - 4 * b * c - 4 * c * d - 4 * d * a := by
          ring
        _ = 5 * (a^2 + b^2 + c^2 + d^2) - 4 * (a * b + b * c + c * d + d * a) := by
          ring
    rw [← h_right_expand, ← h_right, h_left]
  -- Step $6$: Derive $ab + bc + cd + da = a^2 + b^2 + c^2 + d^2$.
  have h_sum_prod_eq : a * b + b * c + c * d + d * a = a^2 + b^2 + c^2 + d^2 := by
    have h_eq : a^2 + b^2 + c^2 + d^2 = 5 * (a^2 + b^2 + c^2 + d^2) - 4 * (a * b + b * c + c * d + d * a) := h_square_sum
    linarith
  -- Step $7$: Prove $(a - b)^2 + (b - c)^2 + (c - d)^2 + (d - a)^2 = 0$.
  have h_sum_squares_zero : (a - b)^2 + (b - c)^2 + (c - d)^2 + (d - a)^2 = 0 := by
    have h_eq : 2 * (a^2 + b^2 + c^2 + d^2) - 2 * (a * b + b * c + c * d + d * a) =
                (a - b)^2 + (b - c)^2 + (c - d)^2 + (d - a)^2 := by
      have h_eq' : (a - b)^2 + (b - c)^2 + (c - d)^2 + (d - a)^2 =
        2 * (a^2 + b^2 + c^2 + d^2) - 2 * (a * b + b * c + c * d + d * a) := by
        calc
          (a - b)^2 + (b - c)^2 + (c - d)^2 + (d - a)^2
          = (a^2 - 2 * a * b + b^2) + (b^2 - 2 * b * c + c^2) +
            (c^2 - 2 * c * d + d^2) + (d^2 - 2 * d * a + a^2) := by
            rw [sq, sq, sq, sq]
            ring
          _ = 2 * a^2 + 2 * b^2 + 2 * c^2 + 2 * d^2 - 2 * a * b - 2 * b * c - 2 * c * d - 2 * d * a := by
            ring
          _ = 2 * (a^2 + b^2 + c^2 + d^2) - 2 * (a * b + b * c + c * d + d * a) := by
            ring
      exact h_eq'.symm
    have h_left : 2 * (a^2 + b^2 + c^2 + d^2) - 2 * (a * b + b * c + c * d + d * a) = 0 := by
      rw [h_sum_prod_eq]
      ring
    rw [← h_eq, h_left]
  -- Step $8$: Therefore, $a = b = c = d$.
  have h_equal : a = b ∧ b = c ∧ c = d := by
    have h_nonneg : (a - b)^2 ≥ 0 ∧ (b - c)^2 ≥ 0 ∧ (c - d)^2 ≥ 0 ∧ (d - a)^2 ≥ 0 := by
      repeat' apply And.intro
      all_goals apply sq_nonneg
    have h_sum_zero : (a - b)^2 + (b - c)^2 + (c - d)^2 + (d - a)^2 = 0 := h_sum_squares_zero
    have h_each_zero : (a - b)^2 = 0 ∧ (b - c)^2 = 0 ∧ (c - d)^2 = 0 ∧ (d - a)^2 = 0 := by
      have h₁ : (a - b)^2 + (b - c)^2 ≥ 0 := by nlinarith
      have h₂ : (c - d)^2 + (d - a)^2  ≥ 0 := by nlinarith
      have h' : (a - b)^2 + (b - c)^2 = 0 ∧ (c - d)^2 + (d - a)^2 = 0 := by
        rw [add_assoc] at h_sum_zero
        exact (add_eq_zero_iff_of_nonneg h₁ h₂).mp h_sum_zero
      have h₁' : (a - b)^2 = 0 ∧ (b - c)^2 = 0 := by
        exact (add_eq_zero_iff_of_nonneg h_nonneg.1 h_nonneg.2.1).mp h'.1
      have h₂' :(c - d)^2 = 0 ∧ (d - a)^2 = 0 := by
        exact (add_eq_zero_iff_of_nonneg h_nonneg.2.2.1 h_nonneg.2.2.2).mp h'.2
      exact And.intro h₁'.1 (And.intro h₁'.2 (And.intro h₂'.1 h₂'.2))
    constructor
    · have : a - b = 0 := by
        have h_ab : (a - b)^2 = 0 := h_each_zero.1
        apply sq_eq_zero_iff.mp
        exact h_ab
      linarith
    constructor
    · have : b - c = 0 := by
        have h_bc : (b - c)^2 = 0 := h_each_zero.2.1
        apply sq_eq_zero_iff.mp
        exact h_bc
      linarith
    · have : c - d = 0 := by
        have h_cd : (c - d)^2 = 0 := h_each_zero.2.2.1
        apply sq_eq_zero_iff.mp
        exact h_cd
      linarith
  exact h_equal
