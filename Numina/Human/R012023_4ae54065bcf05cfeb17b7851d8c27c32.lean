import Mathlib
open Real 
set_option linter.unusedVariables false

/-J.Wolstenholme-embedded inequality: For $\triangle A B C$ and any real numbers $x, y, z$, we have $x^{2}+y^{2}+z^{2} \geq 2 y z \cos A+2 z x \cos B+2 x y \cos C$, (1) where equality holds if and only if $x: y: z=\sin A: \sin B: \sin C$.-/
theorem inequalities_200001 (A B C x y z : ℝ) (h_triangle : A + B + C = Real.pi)
(h_A : 0 < A ∧ A < Real.pi) (h_B : 0 < B ∧ B < Real.pi) (h_C : 0 < C ∧ C < Real.pi) :
(x^2 + y^2 + z^2 ≥ 2 * y * z * Real.cos A + 2 * z * x * Real.cos B + 2 * x * y * Real.cos C) ∧
  (x^2 + y^2 + z^2 = 2 * y * z * Real.cos A + 2 * z * x * Real.cos B + 2 * x * y * Real.cos C ↔
   ∃ k : ℝ, x = k * Real.sin A ∧ y = k * Real.sin B ∧ z = k * Real.sin C) := by
  constructor
  -- Part $1$: Prove the inequality.
  ·   -- Use the triangle angle relation: $cos A = -cos(B + C)$.
    have h_cosA : Real.cos A = -Real.cos (B + C) := by
      rw [← Real.cos_pi_sub (B + C)]
      have h_angle : π - (B + C) = A := by rw [← h_triangle]; ring
      rw [h_angle]
    -- Expand the target expression.
    let expr := x^2 + y^2 + z^2 - (2 * y * z * Real.cos A + 2 * z * x * Real.cos B + 2 * x * y * Real.cos C)
    suffices h_expr : expr ≥ 0 by
      unfold expr at h_expr
      have h_equiv : x^2 + y^2 + z^2 - (2 * y * z * Real.cos A + 2 * z * x * Real.cos B + 2 * x * y * Real.cos C) ≥ 0 ↔
                    x^2 + y^2 + z^2 ≥ 2 * y * z * Real.cos A + 2 * z * x * Real.cos B + 2 * x * y * Real.cos C := by
        constructor
        · intro h
          linarith
        · intro h
          linarith
      exact h_equiv.mp h_expr
    -- Step $1$: Rewrite the expression.
    have h_step1 : expr = (x - y * Real.cos C - z * Real.cos B)^2 + (y * Real.sin C)^2 +
      (z * Real.sin B)^2 - 2 * y * z * Real.cos B * Real.cos C - 2 * y * z * Real.cos A := by
      unfold expr
      ring_nf
      simp [pow_two]
      ring_nf
      have h_trig1 : y^2 * Real.cos C^2 + y^2 * Real.sin C^2 = y^2 := by
        rw [← mul_add]
        simp [Real.cos_sq_add_sin_sq]
      have h_trig2 : z^2 * Real.cos B^2 + z^2 * Real.sin B^2 = z^2 := by
        rw [← mul_add]
        simp [Real.cos_sq_add_sin_sq]
      conv =>
        · left;rw [← h_trig1, ← h_trig2]
      rw [← add_assoc,← add_assoc]
    -- Step 2: Substitute cos $A = -cos(B + C)$.
    have h_step2 : expr = (x - y * Real.cos C - z * Real.cos B)^2 + (y * Real.sin C)^2 +
      (z * Real.sin B)^2 - 2 * y * z * Real.cos B * Real.cos C + 2 * y * z * Real.cos (B + C) := by
      rw [h_step1, h_cosA]
      simp [mul_neg]
    -- Step 3: Rewrite $-2 * y * z * cos B * cos C - 2 * y * z * cos (B + C)$ as $-2 * y * z * sin B * sin C$.
    have h_cos_sum : -2 * y * z * Real.cos B * Real.cos C + 2 * y * z * Real.cos (B + C) =
                  -2 * y * z * Real.sin B * Real.sin C := by
      have h_trig : Real.cos B * Real.cos C - Real.cos (B + C) = Real.sin B * Real.sin C := by
        rw [Real.cos_add]
        ring
      have h_rewrite : -2 * y * z * Real.cos B * Real.cos C + 2 * y * z * Real.cos (B + C) =
                    -2 * y * z * (Real.cos B * Real.cos C - Real.cos (B + C)) := by
        ring
      rw [h_rewrite, h_trig, ← mul_assoc]

    -- Step 4: Substitute to get $expr = (x - y * cos C - z * cos B)^2 + (y * sin C)^2 + (z * sin B)^2 - 2 * y * z * sin B * sin C$.
    have h_step3 : expr = (x - y * Real.cos C - z * Real.cos B)^2 + (y * Real.sin C)^2 +
      (z * Real.sin B)^2 - 2 * y * z * Real.sin B * Real.sin C := by
      have :  2 * y * z * Real.cos B * Real.cos C - 2 * y * z * Real.cos (B + C) =
                  2 * y * z * Real.sin B * Real.sin C := by linarith
      rw [h_step2,sub_add,this]
    -- Step 5: Rewrite as $(x - y * cos C - z * cos B)^2 + (y * sin C - z * sin B)^2$.
    have h_step4 : expr = (x - y * Real.cos C - z * Real.cos B)^2 + (y * Real.sin C - z * Real.sin B)^2 := by
      rw [h_step3]
      have h_expand : (y * Real.sin C)^2 + (z * Real.sin B)^2 - 2 * y * z * Real.sin B * Real.sin C = (y * Real.sin C - z * Real.sin B)^2 := by
        rw [pow_two]
        ring
      rw [← h_expand]
      ring
    -- Conclusion: The expression is a sum of two squares, always non-negative.
    have h_nonneg : (x - y * Real.cos C - z * Real.cos B)^2 + (y * Real.sin C - z * Real.sin B)^2 ≥ 0 := by
      apply add_nonneg
      · apply pow_two_nonneg
      · apply pow_two_nonneg
    rw [← h_step4] at h_nonneg
    exact h_nonneg

  -- Part 2: Prove the equality condition (necessity and sufficiency combined).
  · let expr := x^2 + y^2 + z^2 - (2 * y * z * Real.cos A + 2 * z * x * Real.cos B + 2 * x * y * Real.cos C)
    have h_cosA : Real.cos A = -Real.cos (B + C) := by
      rw [← Real.cos_pi_sub (B + C)]
      have h_angle : π - (B + C) = A := by linarith
      rw [h_angle]
    have h_step1 : expr = (x - y * Real.cos C - z * Real.cos B)^2 + (y * Real.sin C)^2 +
        (z * Real.sin B)^2 - 2 * y * z * Real.cos B * Real.cos C - 2 * y * z * Real.cos A := by
      unfold expr
      ring_nf
      simp [pow_two]
      ring_nf
      have h_trig1 : y^2 * Real.cos C^2 + y^2 * Real.sin C^2 = y^2 := by
        rw [← mul_add, Real.cos_sq_add_sin_sq]
        norm_num
      have h_trig2 : z^2 * Real.cos B^2 + z^2 * Real.sin B^2 = z^2 := by
        rw [← mul_add, Real.cos_sq_add_sin_sq]
        norm_num
      conv =>
        · left;rw [← h_trig1, ← h_trig2]
      ring
    have h_step2 : expr = (x - y * Real.cos C - z * Real.cos B)^2 + (y * Real.sin C)^2 +
        (z * Real.sin B)^2 - 2 * y * z * Real.cos B * Real.cos C + 2 * y * z * Real.cos (B + C) := by
      rw [h_step1, h_cosA]
      simp [mul_neg]
    have h_cos_sum : -2 * y * z * Real.cos B * Real.cos C + 2 * y * z * Real.cos (B + C) =
                    -2 * y * z * Real.sin B * Real.sin C := by
      have h_trig : Real.cos B * Real.cos C - Real.cos (B + C) = Real.sin B * Real.sin C := by
        rw [Real.cos_add]
        ring
      have h_rewrite : -2 * y * z * Real.cos B * Real.cos C + 2 * y * z * Real.cos (B + C) =
                      -2 * y * z * (Real.cos B * Real.cos C - Real.cos (B + C)) := by
        ring
      rw [h_rewrite, h_trig, ← mul_assoc]
    have h_step3 : expr = (x - y * Real.cos C - z * Real.cos B)^2 + (y * Real.sin C)^2 +
        (z * Real.sin B)^2 - 2 * y * z * Real.sin B * Real.sin C := by
      have : 2 * y * z * Real.cos B * Real.cos C - 2 * y * z * Real.cos (B + C) =
            2 * y * z * Real.sin B * Real.sin C := by linarith
      rw [h_step2, sub_add, this]
    have h_step4 : expr = (x - y * Real.cos C - z * Real.cos B)^2 + (y * Real.sin C - z * Real.sin B)^2 := by
      rw [h_step3]
      have h_expand : (y * Real.sin C)^2 + (z * Real.sin B)^2 - 2 * y * z * Real.sin B * Real.sin C =
                      (y * Real.sin C - z * Real.sin B)^2 := by
        rw [pow_two]
        ring
      rw [← h_expand]
      ring
    constructor
    -- Necessity: Equality holds => $x : y : z = sin A : sin B : sin C$.
    · intro h_eq
      have h_expr_eq : expr = 0 := by
        unfold expr
        rw [h_eq]
        ring
      rw [h_step4] at h_expr_eq
      have h_zero : (x - y * Real.cos C - z * Real.cos B)^2 + (y * Real.sin C - z * Real.sin B)^2 = 0 := by
        exact h_expr_eq
      have h_eq1 : x - y * Real.cos C - z * Real.cos B = 0 := by
        have h_a_zero : (x - y * Real.cos C - z * Real.cos B)^2 = 0 := by
          apply le_antisymm
          · have h_nonneg : 0 ≤ (y * Real.sin C - z * Real.sin B)^2 := pow_two_nonneg _
            rw [← h_zero]
            exact le_add_of_nonneg_right h_nonneg
          · apply pow_two_nonneg
        exact pow_eq_zero h_a_zero
      have h_eq2 : y * Real.sin C - z * Real.sin B = 0 := by
        have h_b_zero : (y * Real.sin C - z * Real.sin B)^2 = 0 := by
          apply le_antisymm
          · have h_nonneg : 0 ≤ (x - y * Real.cos C - z * Real.cos B)^2 := pow_two_nonneg _
            rw [← h_zero]
            exact le_add_of_nonneg_left h_nonneg
          · apply pow_two_nonneg
        exact pow_eq_zero h_b_zero
      have h_yz : y * Real.sin C = z * Real.sin B := by
        linarith [h_eq2]
      have h_sinB_pos : 0 < Real.sin B := by apply Real.sin_pos_of_pos_of_lt_pi h_B.1 h_B.2
      have h_sinC_pos : 0 < Real.sin C := by apply Real.sin_pos_of_pos_of_lt_pi h_C.1 h_C.2
      have h_ratio_yz : y / Real.sin B = z / Real.sin C := by
        have h_div : y * Real.sin C / (Real.sin B * Real.sin C) = z * Real.sin B / (Real.sin B * Real.sin C) := by
          rw [h_yz]
        have h₁ : y * Real.sin C / (Real.sin B * Real.sin C) = y / Real.sin B := by
          field_simp [h_sinC_pos]
          ring
        have h₂ : z * Real.sin B / (Real.sin B * Real.sin C) = z / Real.sin C := by
          field_simp [h_sinB_pos]
          ring
        rw [h₁, h₂] at h_div
        exact h_div
      have h_x : x = y * Real.cos C + z * Real.cos B := by linarith
      exists (y / Real.sin B)
      constructor
      · rw [h_x]
        have h_z : z = y * Real.sin C / Real.sin B := by
          rw [h_yz]
          field_simp [h_sinB_pos]
        rw [h_z]
        field_simp [mul_add, mul_comm, mul_assoc]
        have : sin B * (y * (cos C * sin B)) + sin B * (cos B * (y * sin C)) = sin B * y * (sin B * cos C + cos B * sin C) := by
          linarith
        rw [← Real.sin_add B C] at this
        have h_angle : B + C = π - A := by linarith
        rw [h_angle, Real.sin_pi_sub, mul_comm (sin B) y, mul_assoc y (sin B) (sin A), mul_comm (sin B) (sin A)] at this
        exact this
      constructor
      · field_simp [Real.sin_pos_of_pos_of_lt_pi h_B.1 h_B.2]
      · rw [h_ratio_yz]
        field_simp [Real.sin_pos_of_pos_of_lt_pi h_C.1 h_C.2]
    -- Sufficiency: $x : y : z = sin A : sin B : sin C$ => equality holds.
    · rintro ⟨k, h_x, h_y, h_z⟩
      have h_goal : x^2 + y^2 + z^2 = 2 * y * z * Real.cos A + 2 * z * x * Real.cos B + 2 * x * y * Real.cos C ↔ expr = 0 := by
        unfold expr
        constructor
        · intro h
          rw [h]
          ring
        · intro h
          rw [← sub_eq_zero]
          exact h
      suffices h_expr_zero : expr = 0 by
        exact h_goal.mpr h_expr_zero
      rw [h_step4]
      rw [h_x, h_y, h_z]
      simp [pow_two]
      have h_eq1 : k * Real.sin A - k * Real.sin B * Real.cos C - k * Real.sin C * Real.cos B = 0 := by
        rw [sub_sub]
        have : k * sin B * cos C + k * sin C * cos B = k * sin (B + C) := by
          rw [mul_assoc, mul_assoc , ← mul_add, Real.sin_add B C , mul_comm (cos B)  (sin C)]
        rw [this]
        have h_angle : B + C = π - A := by linarith
        rw [h_angle, Real.sin_pi_sub]
        ring
      have h_eq2 : k * Real.sin B * Real.sin C - k * Real.sin C * Real.sin B = 0 := by
        ring
      rw [h_eq1, h_eq2]
      simp