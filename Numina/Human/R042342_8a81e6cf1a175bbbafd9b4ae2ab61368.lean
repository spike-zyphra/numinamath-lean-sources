import Mathlib

/- 1. Solve in integers the equation $\sqrt{x-5}=15-y^{2}$.

Daniela Tilincă and Adriana Mihăilă, Brăila -/

theorem algebra_118463 (x y : ℤ) (hx : 5 ≤ x) :
    Real.sqrt (x - 5) = 15 - y^2 ↔ (x = 230 ∧ y = 0) ∨ (x = 201 ∧ y = 1) ∨ (x = 126 ∧ y = 2) ∨ (x = 41 ∧ y = 3) ∨ (x = 201 ∧ y = -1) ∨ (x = 126 ∧ y = -2) ∨ (x = 41 ∧ y = -3) := by

    constructor

    --From left to right.
    --We have y^2 ≤ 15, so |y| ≤ 3. There are 7 possibilities. We check all of them and get the value of x.
    intro h
    have : 0 ≤ Real.sqrt (x-5) := by exact Real.sqrt_nonneg (↑x - 5)
    have : 0 ≤ 15 - (y:ℝ) ^ 2 := by linarith
    have ineq: y^2 ≤ 15 := by norm_cast at this; linarith
    
    have eq: x = (15 - y^2)^2 + 5 := by 
      have : (x:ℝ) - 5 = (15-y^2)^2 := by 
        have : Real.sqrt (x-5) * Real.sqrt (x-5) = x-5 := by 
          refine Real.mul_self_sqrt ?_; norm_cast; linarith
        rw [<-this] ; rw[h]; ring
      norm_cast at this; linarith
    
    have : y ≤ 3 := by nlinarith
    have : -3 ≤ y := by nlinarith

    by_cases yeq : y = -3
    rw [yeq] at eq; norm_num at eq;
    tauto
    
    by_cases yeq : y = -2
    rw [yeq] at eq; norm_num at eq;
    tauto
    
    by_cases yeq : y = -1
    rw [yeq] at eq; norm_num at eq;
    tauto
    
    by_cases yeq : y = 0
    rw [yeq] at eq; norm_num at eq;
    tauto
    
    by_cases yeq : y = 1
    rw [yeq] at eq; norm_num at eq;
    tauto
    
    by_cases yeq : y = 2
    rw [yeq] at eq; norm_num at eq;
    tauto
    
    have yeq : y = 3 := by omega
    rw [yeq] at eq; norm_num at eq;
    tauto

    -- From right to left. Just simple calculation to show that all of them work.
    intro h
    obtain ⟨xeq,yeq⟩ | ⟨xeq,yeq⟩ | ⟨xeq,yeq⟩ | ⟨xeq,yeq⟩ | ⟨xeq,yeq⟩ | ⟨xeq,yeq⟩ | ⟨xeq,yeq⟩ := h
    
    field_simp [xeq,yeq]; ring_nf; 
    have : (225:ℝ) = 15*15 := by norm_num
    rw [this]
    refine Real.sqrt_mul_self ?_
    linarith

    field_simp [xeq,yeq]; ring_nf; 
    have : (196:ℝ) = 14*14 := by norm_num
    rw [this]
    refine Real.sqrt_mul_self ?_
    linarith

    field_simp [xeq,yeq]; ring_nf; 
    have : (121:ℝ) = 11*11 := by norm_num
    rw [this]
    refine Real.sqrt_mul_self ?_
    linarith

    field_simp [xeq,yeq]; ring_nf; 
    have : (36:ℝ) = 6*6 := by norm_num
    rw [this]
    refine Real.sqrt_mul_self ?_
    linarith

    field_simp [xeq,yeq]; ring_nf; 
    have : (196:ℝ) = 14*14 := by norm_num
    rw [this]
    refine Real.sqrt_mul_self ?_
    linarith

    field_simp [xeq,yeq]; ring_nf; 
    have : (121:ℝ) = 11*11 := by norm_num
    rw [this]
    refine Real.sqrt_mul_self ?_
    linarith

    field_simp [xeq,yeq]; ring_nf; 
    have : (36:ℝ) = 6*6 := by norm_num
    rw [this]
    refine Real.sqrt_mul_self ?_
    linarith