import Mathlib

theorem algebra_196400: {(x, y): ℝ × ℝ | ∃ a b: ℝ, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ x * (a * x ^ 2 + b * y ^ 2 - a) = 0 ∧
    y * (a * x ^ 2 + b * y ^ 2 - b) = 0} = {(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1)} := by
  ext ⟨x, y⟩
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- First: show that if (x,y) is in the system solution, it's in the finite set
    rintro ⟨a, b, ha, hb, hab, hx, hy⟩
    by_cases hx0 : x = 0
    · -- Case x = 0
      simp only [hx0, mul_zero, zero_mul, sub_zero] at hx hy
      simp only [hx0]
      have eq1 : y * (b * (y ^ 2 - 1)) = 0 := by 
        nlinarith
      cases (mul_eq_zero.mp eq1) with 
      | inl h1 =>
        left
        simp [show x = 0 by exact hx0, show y = 0 by linarith]
      | inr h2 =>
        have h2_eq : y ^ 2 - 1 = 0 := by 
          apply (mul_left_inj' hb).mp 
          linarith 
        have h_eq3 : y ^ 2 = 1 := by 
          linarith 
        have hy1 : y = 1 ∨ y = -1 := by 
          have h_eq4 : (y - 1) * (y + 1) = 0 := by 
            nlinarith 
          cases (mul_eq_zero.mp h_eq4) with
          | inl h1 => 
            left 
            linarith 
          | inr h2 => 
            right 
            linarith 
        cases hy1 with 
        | inl hy1 => 
          simp [show x = 0 by exact hx0, show y = 1 by linarith] 
        | inr hy1 => 
          simp [show x = 0 by exact hx0, show y = -1 by linarith] 
    · -- Case x ≠ 0
      have hx_ineq : x ≠ 0 := by 
        intro h
        exfalso 
        tauto 
      have eq1 : a * x ^ 2 + b * y ^ 2 - a = 0 := by 
        apply (mul_right_inj' hx_ineq).mp 
        linarith 
      have eq2 : y * (a - b) = 0 := by 
        have h1 : y * (a * x ^ 2 + b * y ^ 2 - b) = 0 := hy
        have h2 : a * x ^ 2 + b * y ^ 2 - b = a - b := by
          have eq3 : a * x ^ 2 + b * y ^ 2 = a := by 
            linarith [eq1]
          linarith [eq3]
        rw [h2] at h1 
        linarith 
      have hy0 : y = 0 := by 
        have hab_ne : a - b ≠ 0 := by 
          intro h
          apply hab 
          linarith 
        cases (mul_eq_zero.mp eq2) with 
        | inl h => 
          linarith 
        | inr h => 
          exfalso 
          apply hab_ne 
          linarith 
      have eq3 : a * x ^ 2 + b * y ^ 2 - a = 0 := eq1 
      rw [show y = 0 by linarith [hy0]] at eq3 
      have eq4 : a * x ^ 2 - a = 0 := by 
        nlinarith 
      have eq5 : a * (x ^ 2 - 1) = 0 := by 
        nlinarith 
      have eq6 : x ^ 2 - 1 = 0 := by 
        apply (mul_left_inj' ha).mp 
        linarith 
      have eq7 : x ^ 2 = 1 := by 
        linarith 
      have hx1 : x = 1 ∨ x = -1 := by 
        have eq8 : x ^ 2 - 1 = 0 := eq6 
        have eq9 : (x - 1) * (x + 1) = 0 := by 
          nlinarith 
        cases (mul_eq_zero.mp eq9) with 
        | inl h1 => 
          left 
          linarith 
        | inr h2 => 
          right 
          linarith 
      cases hx1 with 
      | inl hx1 => 
        simp [show x = 1 by linarith, show y = 0 by linarith [hy0]
        ]
      | inr hx1 => 
        simp [show x = -1 by linarith, show y = 0 by linarith [hy0]
        ]
  · -- Backward: show that all 5 pairs satisfy the system
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- (0,0)
      use 1, 2 
      norm_num 
    · -- (1,0)
      use 1, 2 
      norm_num 
    · -- (-1,0)
      use 1, 2 
      norm_num 
    · -- (0,1)
      use 1, 2 
      norm_num 
    · -- (0,-1)
      use 1, 2 
      norm_num