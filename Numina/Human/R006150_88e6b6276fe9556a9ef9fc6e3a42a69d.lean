import Mathlib
open Real
/-
Given that the minimum value of $f(x)=\frac{3 \sin x+k}{\cos x+1}\left(k \in \mathbf{R}^{+}\right)$ is $4$, then the value of $k$ is （   ）.

A:$7$

B:$8$

C:$9$

D:$10$
-/

theorem algebra_624323 :
IsLeast {y | ∃ x, (cos x + 1 ≠ 0 ∧ y = (3 * sin x + k) / (cos x + 1))} 4 ↔ k = 9 := by
  unfold IsLeast lowerBounds
  simp

  constructor


  --From left to right, we prove that k = 9.
  intro ⟨h1,h2⟩ 

  --If k > 9, then we show that 4 cannot be achieved.
  have kle9 : k ≤ 9 := by 
    by_contra kg9
    push_neg at kg9
    obtain ⟨x,de,h⟩ := h1
    have : 4 < (3 * sin x + k) / (cos x + 1) := by 
      have t1: 0 < cos x + 1 := by 
        have l1 : -1 ≤ cos x := by exact neg_one_le_cos x
        have l2 : 0 ≤ cos x + 1 := by linarith [l1]
        push_neg at de
        exact lt_of_le_of_ne l2 (id (Ne.symm de))
      have t2: (cos x + 1)*4 < 3 * sin x + k := by 
        have l1 : cos x * 4 - 3 * sin x ≤ 5 := by 
          let y := arcsin (3/5)
          have : cos x * 4 - 3 * sin x = 5 * cos (x+y) := by 
            simp [cos_add, y]
            rw [cos_arcsin]
            rw [sin_arcsin]
            field_simp
            norm_num
            have : √16 = 4 := by refine (sqrt_eq_iff_mul_self_eq_of_pos ?_).mpr ?_; linarith;norm_num
            rw [this]
            ring
            linarith; linarith
          rw [this]
          simp
          exact cos_le_one (x + y)
        linarith
      refine (lt_div_iff₀' ?_).mpr ?_
      exact t1
      exact t2
    linarith

  --If k < 9, then we show that we can get some value smaller than 4. 
  have kge9 : 9 ≤ k := by 
    by_contra kl9 
    push_neg at kl9
    let x := arcsin (-3/5)
    let a := (3 * sin x + k) / (cos x + 1)
    have de: ¬ (cos x + 1 = 0) := by 
      simp [x]
      rw [cos_arcsin]
      field_simp; norm_num
      have : √16 = 4 := by refine (sqrt_eq_iff_mul_self_eq_of_pos ?_).mpr ?_; linarith;norm_num
      rw [this]
      norm_num
    have dep: 0 < cos x + 1 := by 
      have : -1 ≤ cos x := by exact neg_one_le_cos x
      have : 0 ≤ cos x + 1 := by linarith
      push_neg at de
      exact lt_of_le_of_ne this (id (Ne.symm de))
    have : 4 ≤ a := by 
      apply h2
      exact de
      simp [a]
    have : a < 4 := by 
      simp [a,x]
      rw [sin_arcsin, cos_arcsin]
      field_simp; norm_num
      have : √16 = 4 := by refine (sqrt_eq_iff_mul_self_eq_of_pos ?_).mpr ?_; linarith;norm_num
      rw [this]
      ring_nf
      nlinarith
      linarith
      linarith
    linarith
  linarith

  --From right to left, we verify that when k=9, the minimum value of f(x) is indeed 4.
  intro ke
  simp [ke]

  constructor
  
  --4 can be achieved.
  use arcsin (-3/5)
  constructor

  rw [Real.cos_arcsin]
  field_simp
  norm_num
  have : √16 = 4 := by refine (sqrt_eq_iff_mul_self_eq_of_pos ?_).mpr ?_; linarith;norm_num
  rw [this]
  norm_num

  rw [Real.sin_arcsin, Real.cos_arcsin]
  field_simp; norm_num
  have : √16 = 4 := by refine (sqrt_eq_iff_mul_self_eq_of_pos ?_).mpr ?_; linarith;norm_num
  rw [this]
  norm_num
  linarith; linarith

  --4 is a lower bound.
  intro r x de h
  rw [h]
  have l1: 0 < cos x + 1 := by 
    have : -1 ≤ cos x := by exact neg_one_le_cos x
    have : 0 ≤ cos x + 1 := by linarith
    push_neg at de
    exact lt_of_le_of_ne this (id (Ne.symm de))
  have l2: 4*(cos x+ 1) ≤ 3 * (sin x) + 9 := by 
    have t1 : 4 * cos x - 3 * sin x ≤ 5 := by 
      let y := arcsin (3/5)
      have e1 : 4 * cos x - 3 * sin x = 5 * cos (x+y) := by 
        simp [cos_add]
        simp [y]
        rw [cos_arcsin,sin_arcsin]
        field_simp
        norm_num
        have : √16 = 4 := by refine (sqrt_eq_iff_mul_self_eq_of_pos ?_).mpr ?_; linarith;norm_num
        rw [this]
        ring
        linarith; linarith; 
      rw [e1]
      field_simp
      exact cos_le_one (x + y)
    linarith
  exact (le_div_iff₀ l1).mpr l2