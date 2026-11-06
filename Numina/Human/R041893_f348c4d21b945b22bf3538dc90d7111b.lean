import Mathlib

open Real Set
open scoped BigOperators

/- 5. Let the function $f(x), x \in \mathbf{N}$, satisfy $f(x+1)=\sin \left[\frac{\pi}{2} \cdot f(x)\right], f(1)=\frac{1}{2}$, prove that:
$$
1-f(x)<\frac{\pi}{4}[1-f(x-1)](x \geqslant 2) .
$$ -/
theorem algebra_280554 {f : ℕ → ℝ}
  (h₁ : ∀ x, f (x + 1) = sin (π / 2 * f x))
  (h₂ : f 1 = 1 / 2) :
  ∀ x ≥ 1, 1 - f (x + 1) < (π / 4) * (1 - f (x)) := by 
  have eq_aux1 (x : ℕ) (hx : x ≥ 1) : 1 - f (x + 1) = 2 * cos (π * (1 + f x) / (4 : ℝ)) 
    * sin (π * (1 - f x) / (4 : ℝ)) := by 
    rw [h₁ x]
    conv => 
      lhs
      rw [←sin_pi_div_two]
    rw [sin_sub_sin]
    conv => 
      lhs 
      rw [mul_assoc, mul_comm (sin ((π / 2 - π / 2 * f x) / 2)) _, ←mul_assoc]
    have eq_aux1 : cos ((π / 2 + π / 2 * f x) / 2) = cos (π * (1 + f x) / (4 : ℝ)) := by 
      have : ((π / 2 + π / 2 * f x) / 2) = (π * (1 + f x) / (4 : ℝ)) := by 
        nlinarith
      rw [this]
    have eq_aux2 : sin ((π / 2 - π / 2 * f x) / 2) = sin (π * (1 - f x) / (4 : ℝ)) := by
      have : ((π / 2 - π / 2 * f x) / 2) = (π * (1 - f x) / (4 : ℝ)) := by
        nlinarith
      rw [this]
    rw [eq_aux1, eq_aux2]
  have ftwo : f 2 > f 1 := by 
    obtain h1' := h₁ 1
    simp at h1'
    rw [h1', h₂]
    norm_num
    have : π / 2 * (1 / 2) = π / 4 := by nlinarith
    rw [this, sin_pi_div_four]
    have pos : 2 > (0 : ℝ) := by positivity
    have neq : 2 ≠ (0 : ℝ) := by linarith
    field_simp
    have le_aux : 1 < √ 2 := by 
      refine (lt_sqrt ?_).mpr ?_
      positivity
      norm_num
    apply div_lt_div_of_pos_right
    linarith only [le_aux]
    positivity
  have fxbound (x : ℕ) (hx : x ≥ 1) : f x ≥ 1 / 2 ∧ f x < f (x + 1) ∧ f (x + 1) < 1 := by 
    induction x with 
    | zero => 
      simp at hx
    | succ k ih =>
      by_cases hk : k ≥ 1 
      · -- cases k ≥ 1 
        obtain ⟨h1, h2, h3⟩ := ih hk
        -- first case, we show that f(k + 1) is in range (1/2, 1)
        rw [h₁ k]
        have ineq_aux1 : (π / 2) * f k ≥ π / 4 := by 
          calc 
            _ ≥ (π / 2) * (1 / 2) := by exact mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = π / 4 := by nlinarith
        have ineq_aux2 : (π / 2) * f k < π / 2 := by
          calc 
            _ < π / 2 * 1 := by 
              refine (mul_lt_mul_left ?_).mpr ?_
              positivity
              linarith
            _ = π / 2 := by nlinarith
        have ineq_aux3 : (π / 2) * f (k + 1) < π / 2 := by
          calc 
            _ < π / 2 * 1 := by 
              refine (mul_lt_mul_left ?_).mpr ?_
              positivity
              linarith
            _ = π / 2 := by nlinarith
        constructor
        · -- use ineq_aux1 
          calc 
            _ ≥  sin (π / 4) := by 
              apply sin_le_sin_of_le_of_le_pi_div_two
              linarith
              linarith
              linarith
            _ = √2 / 2 := sin_pi_div_four
            _ ≥ 1 / 2 := by 
              have le_aux : 1 <  √ 2 := by 
                refine (lt_sqrt ?_).mpr ?_
                positivity
                norm_num
              linarith
        constructor
        · rw [h₁ (k + 1)]
          apply sin_lt_sin_of_lt_of_le_pi_div_two
          linarith
          nlinarith
          nlinarith
        -- use ineq_aux2
        rw [h₁ (k + 1)]
        calc 
          _ < sin (π / 2 ) := by 
            apply sin_lt_sin_of_lt_of_le_pi_div_two
            repeat nlinarith
          _ = 1 := by rw [sin_pi_div_two]
      · -- cases k < 1 
        have kzero : k = 0 := by omega
        rw [kzero]
        simp
        constructor
        rw [h₂]
        simp
        constructor
        simpa
        obtain h1' := h₁ 1
        simp at h1'
        rw [h1', h₂]
        norm_num
        have : π / 2 * (1 / 2) = π / 4 := by nlinarith
        rw [this, sin_pi_div_four]
        have one_eq : 1 = (2 : ℝ) / (2 : ℝ) := by norm_num
        rw [one_eq]
        have le_aux : √ 2 < 2 := by 
          refine (sqrt_lt' ?_).mpr ?_
          positivity
          norm_num
        apply div_lt_div_of_pos_right
        linarith only [le_aux]
        positivity
  have ineq_aux1 (x : ℕ) (hx : x ≥ 1)  : π / 4 * (1 + f x) ≥ 3 * π / 8 ∧ π / 4 * (1 + f x) < π / 2 := by 
    obtain ⟨h1, h2, h3⟩ := fxbound x hx
    constructor
    calc 
      _ ≥ π / 4 * ( 3 / (2 : ℝ)) := by 
        apply mul_le_mul
        simp
        linarith
        linarith
        positivity
      _ = _ := by nlinarith
    calc 
      _ < π / 4 * 2 := by 
        refine (mul_lt_mul_left ?_).mpr ?_
        positivity
        linarith
      _ = π / 2 := by nlinarith
  have cos_aux (x : ℕ) (hx : x ≥ 1) : cos (π / 4 * (1 + f x)) > 0 ∧ cos (π / 4 * (1 + f x)) < 1 / 2 := by 
    obtain ⟨h1, h2⟩ := ineq_aux1 x hx
    constructor
    rw [←cos_pi_div_two]
    apply cos_lt_cos_of_nonneg_of_le_pi
    linarith
    linarith
    linarith
    rw [←cos_pi_div_three]
    apply cos_lt_cos_of_nonneg_of_le_pi
    linarith
    linarith
    linarith
  have cos_aux2 (x : ℕ) (hx : x ≥ 1) : 2 * cos (π / 4 * (1 + f x)) > 0 ∧ 2 * cos (π / 4 * (1 + f x)) < 1 := by 
    obtain ⟨h1, h2⟩ := cos_aux x hx
    constructor
    linarith
    linarith
  have ineq_aux2 (x : ℕ) (hx : x ≥ 1): 1 - f (x + 1) < sin (π * (1 - f x) / (4 : ℝ)) := by 
    rw [eq_aux1 x hx]
    obtain ⟨h1, h2⟩ := cos_aux2 x hx
    calc 
      _ < 1 * sin (π * (1 - f x) / 4) := by 
        have aux : 2 * cos (π * (1 + f x) / 4) < 1 := by 
          have eq_aux : π * (1 + f x) / 4 = π / 4 * (1 + f x) := by ring
          rw [eq_aux]
          linarith
        refine (mul_lt_mul_right ?_).mpr aux
        obtain ⟨h1, h2, h3⟩ := fxbound x hx
        rw [←sin_zero]
        apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
        have : π / 2 ≥ 0 := by positivity
        linarith
        have fle : 1 - f x ≤ 1 := by 
          linarith
        calc 
          _ ≤ π * 1 / 4 := by 
            field_simp
            refine (div_le_div_iff_of_pos_right ?_).mpr ?_
            linarith
            conv =>
              rhs 
              rw [←mul_one π]
            apply mul_le_mul_of_nonneg_left
            linarith
            positivity
          _ ≤ π / 2 := by 
            field_simp
            apply div_le_div_of_nonneg_left
            positivity
            linarith
            linarith
        have : 1 - f x > 0 := by linarith
        have pos : π > 0 := by positivity
        nlinarith
      _ = _ := by simp
    
  have ineq_aux3 (x : ℕ) (hx : x ≥ 1):  (π * (1 - f x) / (4)) ≤ π / 8 ∧ π * (1 - f x) / 4 > 0 := by 
    obtain ⟨h1, h2, h3⟩ := fxbound x hx
    constructor
    · have fle : 1 - f x ≤ (1 / 2) := by 
        linarith
      calc 
        _ ≤ π * (1 / 2) / 4 := by 
          refine (div_le_div_iff_of_pos_right ?_).mpr ?_
          linarith
          apply mul_le_mul_of_nonneg_left
          linarith
          positivity
        _ ≤ π / 8 := by 
          field_simp
          apply div_le_div_of_nonneg_left
          positivity
          linarith
          linarith
    have : 1 - f x > 0 := by linarith
    have pos : π > 0 := by positivity
    nlinarith
  have ineq_aux4 (x : ℕ) (hx : x ≥ 1): sin (π * (1 - f x) / (4 : ℝ)) ≤ (π * (1 - f x) / (4 : ℝ)) := by 
    apply sin_le
    obtain ⟨h1, h2, h3⟩ := fxbound x hx
    have : (1 - f x ) > 0 := by linarith
    positivity
  intro x hx
  calc 
    _ < sin (π * (1 - f x) / (4 : ℝ)) := ineq_aux2 x hx
    _ ≤ (π * (1 - f x) / (4 : ℝ)) := ineq_aux4 x hx
    _ = π / 4 * (1 - f x) := by 
      ring
