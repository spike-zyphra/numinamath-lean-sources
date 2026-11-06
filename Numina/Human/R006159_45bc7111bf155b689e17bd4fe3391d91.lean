import Mathlib

open ProbabilityTheory

/-
When $a$ takes the values $-2$, $-1$, $0$, $1$, $2$, $3$, $\cdots $, $97$ (these $100$ numbers), the probability that the fractional equation $\frac{1}{x-1}-\frac{a}{2-x}=\frac{2(a+1)}{{x}^{2}-3x+2}$ has a solution is ___          ___ .
-/

theorem algebra_625273:
(uniformOn (Finset.Icc (-2) 97)) {a:ℤ | -2 ≤ a ∧ a ≤ 97 ∧ (∃x:ℝ, ((x:ℝ)-1 ≠ 0) ∧ (2-x)≠ 0 ∧ (x^2-3*x+2) ≠ 0 ∧ 1/((x:ℝ)-1) - a / (2-x) = (2*(a+1))/(x^2-3*x+2))} = 49/50 := by 
  
  --We prove that it has a solution when a ∈ [0.97].
  have cla1 : {a:ℤ | -2 ≤ a ∧ a ≤ 97 ∧ (∃x:ℝ, ((x:ℝ)-1 ≠ 0) ∧ (2-x)≠ 0 ∧ (x^2-3*x+2) ≠ 0 ∧ 1/((x:ℝ)-1) - a / (2-x) = (2*(a+1))/(x^2-3*x+2))} = Finset.Icc (0:ℤ) 97 := by 
    ext a
    simp

    constructor

    --We just need to prove that -1 and -2 do not work.
    intro h
    obtain ⟨agem2, ale97, h⟩ := h
    obtain ⟨x, hx1, hx2, hx3, h⟩ := h
    field_simp at h
    have : 2 * (↑a + 1) * ((x - 1) * (2 - x)) = (- 2* ((a:ℝ) +1)) * (x^2 - 3*x + 2) := by ring
    rw [this] at h
    apply mul_right_cancel₀ at h
    
    have c1 : a ≠ -1 := by 
      by_contra aem1
      rw [aem1] at h
      field_simp at h
      norm_num at h
    have c2 : a ≠ -2 := by 
      by_contra aem2
      rw [aem2] at h
      field_simp at h
      ring_nf at h
      rw [h] at hx2
      simp at hx2
    omega
    simp
    exact hx3

    --All others work.
    intro h
    obtain ⟨hl, hu⟩ := h
    constructor
    linarith
    constructor
    linarith
    use (3*a+4)/(a+1)
    field_simp
    ring_nf
    field_simp
    have t1 : ¬3 + (a:ℝ) * 2 = 0 := by norm_cast; omega
    have t2 : ¬-2 - (a:ℝ) = 0 := by norm_cast; simp; omega
    have t3 : ¬6 + (a:ℝ) * 13 + ↑a ^ 2 * 9 + ↑a ^ 3 * 2 = 0 := by norm_cast; nlinarith
    have t4 : ¬ (3 + (a:ℝ) * 2)* (-2 - ↑a) = 0 := by 
      by_contra h
      simp [t1,t2] at h
    simp [t1,t2,t3,t4]
    field_simp
    ring
    
  --The remaining part is just to use the definition of probability. The space is finite so we can directly use the definition.
  rw [cla1]
  simp
  rw [ProbabilityTheory.uniformOn]
  rw [ProbabilityTheory.cond_apply]

  have : Set.Icc (-2) 97 ∩ Set.Icc 0 97 = Set.Icc 0 97 := by 
    simp
    intro x
    intro h
    simp at h ⊢
    obtain ⟨h1,h2⟩ := h
    constructor <;> linarith
  rw [this]


  have e1: (MeasureTheory.Measure.count (Set.Icc (-2) 97)) = 100 := by 
    rw [MeasureTheory.Measure.count_apply]
    simp
    have : (Set.Icc (-2) 97).encard = 100 := by
      have : (Set.Icc (-2) 97).encard = (Finset.Icc (-2) 97).card := by 
        have : (Set.Icc (-2) 97) = (Finset.Icc (-2) 97) := by simp
        rw [this]
        exact Set.encard_coe_eq_coe_finsetCard (Finset.Icc (-2) 97)
      rw [this]
      simp
    simp [this]
    trivial
  have e2 : (MeasureTheory.Measure.count (Set.Icc (0:ℤ) 97)) = 98 := by 
    rw [MeasureTheory.Measure.count_apply]
    simp
    have : (Set.Icc (0:ℤ) 97).encard = 98 := by
      have : (Set.Icc (0:ℤ) 97).encard = (Finset.Icc (0:ℤ) 97).card := by 
        have : (Set.Icc (0:ℤ) 97) = (Finset.Icc (0:ℤ) 97) := by simp
        rw [this]
        exact Set.encard_coe_eq_coe_finsetCard (Finset.Icc 0 97)
      rw [this]
      simp
    simp [this]
    trivial

  rw [e1,e2]
  field_simp
  norm_cast
  rw [@ENNReal.mul_comm_div]
  simp
  have : @OfNat.ofNat ENNReal 98 instOfNatAtLeastTwo = 2*49 := by norm_num
  rw [this]
  have : @OfNat.ofNat ENNReal 100 instOfNatAtLeastTwo = 2 * 50:= by norm_num
  rw [this]
  refine ENNReal.mul_div_mul_left 49 50 ?_ ?_
  simp
  simp
  trivial

  
