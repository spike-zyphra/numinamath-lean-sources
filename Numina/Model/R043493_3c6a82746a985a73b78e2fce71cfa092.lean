import Mathlib

theorem algebra_258971 :
  {x : ℝ | 0 ≤ 7 * x ^ 2 - 5 * x + 1 ∧ 
   5 * x - 7 * x ^ 2 + 8 * Real.sqrt (7 * x ^ 2 - 5 * x + 1) = 8} =
  {0, 5/7, 3, -16/7} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- First direction: If x is in the left side, then in the right side
    rintro ⟨h1, h2⟩
    have h1 : 0 ≤ 7 * x ^ 2 - 5 * x + 1 := h1
    have h4 : 5 * x -7 * x^2 +8 * Real.sqrt (7 * x ^ 2 -5 *x +1) =8 := h2
    have h7 : (Real.sqrt (7*x ^ 2 -5*x +1)) ^2 =7 * x^2 -5*x +1 := Real.sq_sqrt (show 7*x ^2 -5*x +1 ≥0 by assumption)
    have h8 : (Real.sqrt (7 * x ^ 2 -5 *x +1) -7)*(Real.sqrt (7 * x ^ 2 -5 *x +1) -1) =0 := by
      nlinarith
    cases' (mul_eq_zero.mp h8) with h9 h10
    · -- Case h9: Real.sqrt (7 * x ^2 -5 *x +1) -7=0
      have h11 : Real.sqrt (7 * x ^ 2 -5 *x +1) =7 := by linarith
      have h12 :7*x^2 -5*x +1=49 := by
        nlinarith [h11, Real.sqrt_nonneg (7*x^2-5*x+1)]
      have :x=3 ∨x=-16/7 :=by
        have h :7*x^2 -5*x -48=0 := by linarith
        have :7*(x -3)*(x +16/7)=0 := by
          nlinarith
        cases' (mul_eq_zero.mp this) with h14 h15
        · -- 7*(x -3) =0
          have h16 :x -3=0 := by nlinarith
          left
          linarith
        · -- 7*(x +16/7)=0
          have h17 :x +16/7=0 := by nlinarith
          right
          linarith
      cases this with
      | inl h18 =>
        tauto
      | inr h19 =>
        tauto
    · -- Case h10: Real.sqrt (7 *x ^ 2 -5 *x +1) -1=0
      have h14 : Real.sqrt (7*x^2 -5 *x +1) =1 := by linarith
      have h15 :7 *x^2 -5*x +1=1 := by
        nlinarith [h14, Real.sqrt_nonneg (7*x^2-5*x+1)]
      have :x=0 ∨x=5/7 :=by
        have h :7*x^2 -5*x =0 := by linarith
        have :x*(7*x -5)=0 :=by
          nlinarith
        cases' (mul_eq_zero.mp this) with h18 h19
        · -- x * ... =0 =>x=0
          left
          linarith
        · -- 7x -5=0
          right
          linarith
      cases this with
      | inl h16 =>
        tauto
      | inr h17 =>
        tauto
  · -- Backward direction: If x is in the right side, then in the left side
    rintro (rfl | rfl | rfl | rfl)
    · -- x = 0
      constructor
      · -- Show 0 ≤7 *0 ^2 -5 *0 +1
        norm_num
      · -- Show 5 *0 -7 *0 ^2 +8 *Real.sqrt (7*0^2 -5 *0 +1) =8
        have h2 : Real.sqrt (7 * (0 : ℝ) ^2 -5 * (0 : ℝ) +1) = 1 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        nlinarith [h2]
    · -- x = 5/7
      constructor
      · -- Show 0 ≤7*(5/7)^2 -5*(5/7) +1
        norm_num
      · -- Show 5*(5/7) -7*(5/7)^2 +8*Real.sqrt (7*(5/7)^2 -5*(5/7) +1)=8
        have h1 : Real.sqrt (7*(5/7)^2 -5*(5/7)+1) =1 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        nlinarith [h1]
    · -- x = 3
      constructor
      · -- Show 0 ≤7*(3)^2 -5*(3) +1
        norm_num
      · -- Show 5*3 -7*3^2 +8*Real.sqrt (7*3^2 -5*3 +1) =8
        have h1 : Real.sqrt (7*(3:ℝ)^2 -5*(3:ℝ) +1) =7 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        nlinarith [h1]
    · -- x = -16/7
      constructor
      · -- Show 0 ≤7*(-16/7)^2 -5*(-16/7) +1
        norm_num
      · -- Show 5*(-16/7) -7*(-16/7)^2 +8 * Real.sqrt (7*(-16/7)^2 -5*(-16/7)+1) =8
        have h1 : Real.sqrt (7*(-16/7)^2 -5*(-16/7)+1) =7 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        nlinarith [h1]