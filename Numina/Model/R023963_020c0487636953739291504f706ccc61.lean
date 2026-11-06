import Mathlib

theorem algebra_243515 {x y z : ℝ} :
    x^2 - y = z^2 ∧ y^2 - z = x^2 ∧ z^2 - x = y^2 ↔
    (x = 0 ∧ y = 0 ∧ z = 0) ∨ (x = 1 ∧ y = 0 ∧ z = -1) ∨
    (x = 0 ∧ y = -1 ∧ z = 1) ∨ (x = -1 ∧ y = 1 ∧ z = 0) := by 
  constructor
  · -- Assume the conjunction of the three equations, prove the disjunction of the solutions
    rintro ⟨h1, h2, h3⟩
    have h4 : x + y + z = 0 := by
      nlinarith
    have hz : z = -x - y := by linarith 
    rw [hz] at h1
    have eq1 : y * (y + 2 * x + 1) = 0 := by 
      nlinarith
    cases (mul_eq_zero.1 eq1) with
    | inl hy0 =>
      have hy : y = 0 := hy0 
      have hz0 : z = -x := by 
        rw [hy] at hz 
        linarith 
      rw [hy, hz0] at h2 
      have eq1 : x * (x - 1) = 0 := by 
        nlinarith 
      cases (mul_eq_zero.1 eq1) with
      | inl hx0 =>
        have hx : x = 0 := hx0
        have hz00 : z = 0 := by 
          rw [hx] at hz0
          linarith 
        left 
        constructor 
        · linarith 
        constructor 
        · linarith 
        · linarith 
      | inr hx1 =>
        have hx : x = 1 := by 
          nlinarith 
        have hz00 : z = -1 := by 
          rw [hx] at hz0
          linarith 
        right 
        left 
        constructor 
        · linarith 
        constructor 
        · linarith 
        · linarith 
    | inr hy1 =>
      have h_eq2 : y = -2 * x - 1 := by linarith 
      rw [hz] at h2 
      rw [h_eq2] at h2 
      have eq2 : 3 * x * (x + 1) = 0 := by 
        nlinarith 
      cases (mul_eq_zero.1 eq2) with
      | inl hx0 =>
        have hx : x = 0 := by 
          linarith 
        have hy : y = -1 := by 
          rw [hx] at h_eq2 
          linarith 
        have hz1 : z = 1 := by 
          have h_eq2' : y = -1 := hy 
          rw [hx] at hz 
          nlinarith 
        right 
        right 
        left 
        constructor 
        · linarith 
        constructor 
        · linarith 
        · linarith 
      | inr hx1 =>
        have hx : x = -1 := by 
          linarith 
        have hy : y = 1 := by 
          rw [hx] at h_eq2 
          linarith 
        have hz0 : z = 0 := by 
          rw [hx] at hz 
          nlinarith 
        right 
        right 
        right 
        constructor 
        · linarith 
        constructor 
        · linarith 
        · linarith 
  · -- Assume the disjunction of the solutions, prove the conjunction of the equations
    rintro (h | h | h | h)
    · -- First solution (0, 0, 0)
      rcases h with ⟨hx, hy, hz⟩
      constructor
      · -- First equation
        rw [hx, hy, hz]
        norm_num 
      constructor
      · -- Second equation
        rw [hx, hy, hz]
        norm_num 
      · -- Third equation
        rw [hx, hy, hz]
        norm_num 
    · -- Second solution (1, 0, -1)
      rcases h with ⟨hx, hy, hz⟩
      constructor 
      · -- First equation
        rw [hx, hy, hz]
        norm_num 
      constructor 
      · -- Second equation
        rw [hx, hy, hz]
        norm_num 
      · -- Third equation
        rw [hx, hy, hz]
        norm_num 
    · -- Third solution (0, -1, 1)
      rcases h with ⟨hx, hy, hz⟩
      constructor 
      · -- First equation
        rw [hx, hy, hz]
        norm_num 
      constructor 
      · -- Second equation
        rw [hx, hy, hz]
        norm_num 
      · -- Third equation
        rw [hx, hy, hz]
        norm_num 
    · -- Fourth solution (-1, 1, 0)
      rcases h with ⟨hx, hy, hz⟩
      constructor 
      · -- First equation
        rw [hx, hy, hz]
        norm_num 
      constructor 
      · -- Second equation
        rw [hx, hy, hz]
        norm_num 
      · -- Third equation
        rw [hx, hy, hz]
        norm_num