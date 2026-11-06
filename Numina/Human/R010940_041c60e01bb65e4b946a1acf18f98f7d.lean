import Mathlib

/-
A nonzero polynomial $f(x)$ with real coefficients has the property that $f(x)=f^{\prime}(x) f^{\prime \prime}(x)$. What is the leading coefficient of $f(x)$ ?
-/

theorem algebra_611434 (f: Polynomial ℝ) (hf : f ≠ 0)  (h : f = (f.derivative) * (f.derivative).derivative) : f.leadingCoeff = 1 / 18 := by

  -- a lot of basic facts needed later
  have fleadingneq0: f.leadingCoeff ≠ 0 := by exact Polynomial.leadingCoeff_ne_zero.mpr hf
  have fddneq0 : (f.derivative).derivative ≠ 0 := by 
    by_contra eq; rw [eq] at h; simp at h; contradiction
  have fdneq0 : f.derivative ≠ 0 := by by_contra eq; rw [eq] at h; simp at h; contradiction
  have : f.derivative.natDegree ≠ 0 := by 
    by_contra fdnatdeq0
    have : f.derivative.derivative = 0 := by exact Polynomial.derivative_of_natDegree_zero fdnatdeq0
    contradiction
  have fddp: 0 < f.derivative.natDegree := by exact Nat.zero_lt_of_ne_zero this
  have : f.natDegree ≠ 0 := by 
    by_contra fndeq0
    have : f.derivative = 0 := by exact Polynomial.derivative_of_natDegree_zero fndeq0
    contradiction
  have fdp: 0 < f.natDegree := by exact Nat.zero_lt_of_ne_zero this
  have myeq: f.leadingCoeff = (f.derivative).leadingCoeff * ((f.derivative).derivative).leadingCoeff := by 
    nth_rw 1 [h];
    apply Polynomial.leadingCoeff_mul;
  have leadingMul : (f.derivative).leadingCoeff * ((f.derivative).derivative).leadingCoeff ≠ 0 := by
    by_contra muleq0
    have : (f.derivative).leadingCoeff = 0 ∨ ((f.derivative).derivative).leadingCoeff = 0 := by exact mul_eq_zero.mp muleq0
    have : f = 0 := by
      obtain h1|h2 := this
      rw [h1] at myeq; ring_nf at myeq; 
      simp [Polynomial.leadingCoeff_eq_zero] at myeq; assumption
      rw [h2] at myeq; ring_nf at myeq
      simp [Polynomial.leadingCoeff_eq_zero] at myeq; assumption
    contradiction
  have tmp1 : (f.derivative).natDegree = f.natDegree - 1 := by 
    have l1: f.derivative.degree = ↑ (f.natDegree - 1) := by 
      exact Polynomial.degree_derivative_eq f fdp
    have l2: (f.derivative).natDegree = f.derivative.degree := by exact Eq.symm (Polynomial.degree_eq_natDegree fdneq0)
    rw [l1] at l2; simp at l2; assumption      
  have tmp2 : (f.derivative).derivative.natDegree = f.natDegree - 2 := by 
    have s1: (f.derivative).derivative.natDegree = f.derivative.natDegree - 1:= by 
      have l1: f.derivative.derivative.degree = ↑ (f.derivative.natDegree - 1) := by apply Polynomial.degree_derivative_eq; assumption
      have l2: (f.derivative.derivative).natDegree = f.derivative.derivative.degree := by exact Eq.symm (Polynomial.degree_eq_natDegree fddneq0)
      rw [l1] at l2; simp at l2; assumption
    rw [tmp1] at s1; rw [s1]; omega


  -- The degree of f is 3, which follows from the assumption h directly.
  have fd3: f.natDegree = 3 := by 
    have degmul: f.natDegree = (f.derivative).natDegree +
     (((f.derivative).derivative).natDegree) := by 
      nth_rw 1 [h];
      apply Polynomial.natDegree_mul'; assumption
    rw [tmp1,tmp2] at degmul; ring_nf at degmul; 
    omega
  have fdd2 : f.derivative.natDegree = 2 := by rw [tmp1]; omega
  have fddd1 : f.derivative.derivative.natDegree =1 := by rw [tmp2]; omega

  -- the connection between leading terms
  have tmp1: (f.derivative).leadingCoeff = 3 * f.leadingCoeff := by 
    have l1 : f.derivative.coeff 2 = f.coeff (2+1) * (↑2 + 1) := by apply Polynomial.coeff_derivative
    ring_nf at l1; rw [mul_comm] at l1
    have l2: f.derivative.coeff f.derivative.natDegree = f.derivative.leadingCoeff := by exact rfl
    rw [fdd2] at l2; rw[l2] at l1
    have l3: f.coeff f.natDegree = f.leadingCoeff := by exact rfl
    rw [fd3] at l3; rw [l3] at l1; 
    assumption
  have tmp2: (f.derivative).derivative.leadingCoeff = 6 * f.leadingCoeff := by
    have ttmp2 : f.derivative.derivative.leadingCoeff = 2 * f.derivative.leadingCoeff := by 
      have l1 : (f.derivative).derivative.coeff 1 = ((f.derivative).coeff (1+1)) * ((@Nat.cast ℝ AddMonoidWithOne.toNatCast 1 : ℝ) + 1) := by exact Polynomial.coeff_derivative f.derivative 1;
      ring_nf at l1; rw [mul_comm] at l1
      have l2: f.derivative.derivative.coeff f.derivative.derivative.natDegree = f.derivative.derivative.leadingCoeff := by exact rfl
      rw [fddd1] at l2; rw[l2] at l1
      have l3: f.derivative.coeff f.derivative.natDegree = f.derivative.leadingCoeff := by exact rfl
      rw [fdd2] at l3; rw [l3] at l1;
      assumption       
    rw [tmp1] at ttmp2; ring_nf at ttmp2; rw [mul_comm]; assumption

  -- solving the equation and get the leading term.
  rw [tmp1, tmp2] at myeq; ring_nf at myeq; rw [pow_two] at myeq
  nth_rw 1 [←mul_one f.leadingCoeff] at myeq
  have res: 1 = f.leadingCoeff * 18 := by rw [mul_assoc] at myeq; field_simp [fleadingneq0] at myeq; symm; assumption
  nlinarith


