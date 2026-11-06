import Mathlib

/- Vind alle functies $f: \mathbb{R} \rightarrow \mathbb{R}$ met

$$
\left(x^{2}+y^{2}\right) f(x y)=f(x) f(y) f\left(x^{2}+y^{2}\right)
$$

voor alle reële $x$ en $y$. -/
theorem algebra_605525 {f : ℝ → ℝ} : (∀ x y, (x ^ 2 + y ^ 2) * f (x * y) = f x * f y * f (x ^ 2 + y ^ 2)) ↔ (∀ x, f x = 0) ∨ (∀ x, f x = x) ∨ (∀ x, f x = -x) ∨ (∀ x, f x = abs x) ∨ (∀ x, f x = -abs x) := by 

  constructor

  --Frome left to right. We do it by dividing it into 3 cases : x = 0, x > 0, and x < 0.
  intro h

  --f 0 = 0
  have f0 : f 0 = 0 := by
    specialize h 0 0
    ring_nf at h
    exact pow_eq_zero (id (Eq.symm h))

  by_cases feq0Other : ∃ a ≠ 0, f a = 0
  obtain ⟨a,ha,fa0⟩ := feq0Other
  specialize h a
  rw [fa0] at h; norm_num at h
  have : ∀y:ℝ, f (a*y) = 0 := by 
    intro y
    specialize h y
    rcases h with h | h
    have : a = 0 := by nlinarith
    contradiction
    assumption
  left
  intro x
  specialize this (x/a)
  field_simp [ha] at this
  assumption

  --For x > 0, we prove that f x = (f 1 ) * x.
  --The proof is further divided into 3 cases: x=1, x > 1 and x <1. In each case, we use the assumption to verify it separately.
  have fneq0neq0 := by push_neg at feq0Other; exact feq0Other
  have f1n0 : f 1 ≠ 0 := by apply fneq0neq0; norm_num
  have cla1 : ∀ x > 1, (f x) = x / (f 1) := by 
    have t1: ∀ x≠0, (x^2+1)* (f x) = (f x) * (f 1) * (f (x^2+1)) := by 
      intro x hx
      have : (x ^ 2 + 1 ^ 2) * f (x * 1) = f x * f 1 * f (x ^ 2 + 1 ^ 2) := by apply h
      field_simp at this; assumption
    have t2: ∀ x≠0, (x^2+1) = (f 1) * (f (x^2+1)) := by 
      intro x hx
      have fxneq0: f x ≠ 0 := by apply fneq0neq0; assumption
      have : (x^2+1)* (f x) = (f x) * (f 1) * (f (x^2+1)) := by apply t1; assumption
      rw [mul_comm] at this; rw [mul_assoc] at this
      apply mul_left_cancel₀ at this
      assumption; assumption
    intro x hx
    specialize t2 (Real.sqrt (x-1))
    have t3 : Real.sqrt (x-1) ≠ 0 := by refine Real.sqrt_ne_zero'.mpr ?_; linarith
    apply t2 at t3
    have t4 : (Real.sqrt (x-1))^2 = x-1 := by refine Real.sq_sqrt ?_; linarith
    rw [t4] at t3; ring_nf at t3 ⊢; nth_rw 2 [t3]
    field_simp
  
  have f2 : f 2 = 2 / f 1 := by apply cla1; linarith
  have cla20: (f 1)^2 = 1 := by
    have f4 : f 4 = 4 / f 1 := by apply cla1; linarith
    have f8 : f 8 = 8 / f 1 := by apply cla1; linarith
    specialize h 2 2; ring_nf at h
    rw [f2, f4, f8] at h;
    field_simp [f1n0] at h; ring_nf at h; field_simp at h
    have : 3 = (2).succ := by norm_num
    rw [this] at h; 
    rw [pow_succ] at h
    have : f 1 = 1 * f 1 := by norm_num
    nth_rw 3 [this] at h
    apply mul_right_cancel₀ at h
    assumption; assumption
  have cla2: f 1 = 1 ∨ f 1 = -1 := by exact sq_eq_one_iff.mp cla20

  have cla3 : ∀ x > 0 , f (x) = f 1 * x := by 
    have t1: ∀ x > 1, f x = f 1 * x := by
      intro x hx
      have t2: f x = x / f 1 := by apply cla1; assumption
      have t3: x / f 1 = f 1 * x := by 
        field_simp; nth_rw 2[mul_comm]; rw [mul_assoc];
        have : f 1 * f 1 = 1 := by rw [pow_two] at cla20; assumption
        rw [this]; ring
      rw [← t3]; assumption
    have t4: ∀ x > 1, f (1/x) = f 1 * (1/x) := by
      intro x hx
      specialize h x (1/x)
      have a1 : x * (1/x) = 1 := by field_simp
      rw [a1] at h
      have : (x^2 + (1/x)^2 >1) := by nlinarith
      apply t1 at this
      rw [this] at h;
      have : f x = f 1 * x := by
        apply t1; assumption
      rw [this] at h
      obtain cla2 | cla2 := cla2
      rw [cla2] at h ⊢; field_simp at h ⊢
      rw [mul_comm]; assumption
      rw [cla2] at h ⊢; field_simp at h ⊢
      have : 1 + (x^2*x^2) = -(x * f (1/x)) * (1 + (x^2*x^2)) := by linarith
      have : 1 * (1 + (x^2*x^2)) = -(x * f (1/x)) * (1 + (x^2*x^2)) := by linarith
      apply mul_right_cancel₀ at this; 
      ring_nf at this ⊢
      rw [this]; ring;
      nlinarith
      
    intro x hx
    by_cases xg1: x > 1
    apply t1 at xg1; assumption
    by_cases xeq1: x = 1
    rw [xeq1]; ring
    have xl1 : x < 1 := by push_neg at xg1 xeq1; exact lt_of_le_of_ne xg1 xeq1
    have : 1/x > 1 := by exact one_lt_one_div hx xl1
    apply t4 at this; field_simp at this; assumption

  have cla5 : f (-1) = 1 ∨ f (-1) = -1 := by 
    specialize h (-1) (-1)
    field_simp at h; ring_nf at h; 
    have : f 2 = f 1 * 2 := by apply cla3; linarith
    rw [this] at h
    field_simp at h
    assumption

  --For x < 0, we prove that f x = -(f (-1)) * x.
  have cla4 : ∀ x < 0 , f (x) = -f (-1) * x := by
    intro x hx
    specialize h (-x) (-1)
    field_simp at h
    have : f (-x) = f 1 * (-x) := by apply cla3; linarith
    rw [this] at h
    have : f (x^2+1) = f 1 * (x^2+1) := by apply cla3; nlinarith
    rw [this] at h
    rcases cla2 with cla2 | cla2
    rw [cla2] at h; field_simp at h
    nlinarith
    rw [cla2] at h; field_simp at h
    nlinarith

  --Now, depending on the value of f 1 and f (-1), we get the expression of f x.
  rcases cla2 with h11 | h1m1
  rcases cla5 with hm11|hm1m1
  right;right;right;left;
  intro x;
  by_cases xpos : 0 < x
  have : |x| = x := by apply abs_of_pos;assumption
  rw [this];
  have : f x = f 1 * x := by apply cla3; linarith
  rw [h11] at this; field_simp at this; assumption
  by_cases xe0 : x = 0
  simp [xe0, f0]
  have xneg: x <0 := by push_neg at xpos xe0; exact lt_of_le_of_ne xpos xe0
  have : |x| = -x := by apply abs_of_neg;exact xneg
  rw [this]
  have : f x = -(f (-1)) * x := by apply cla4; assumption
  simp [hm11] at this; assumption

  right; left
  intro x
  by_cases xpos : 0 < x
  have : f x = f 1 * x := by apply cla3; linarith
  rw [h11] at this; field_simp at this; assumption
  by_cases xe0 : x = 0
  simp [xe0, f0]
  have xneg: x <0 := by push_neg at xpos xe0; exact lt_of_le_of_ne xpos xe0
  have : f x = -(f (-1)) * x := by apply cla4; assumption
  simp [hm1m1] at this; assumption

  rcases cla5 with hm11 | hm1m1
  right;right;left;
  intro x
  by_cases xpos : 0 < x
  have : f x = f 1 * x := by apply cla3; linarith
  rw [h1m1] at this; field_simp at this; assumption
  by_cases xe0 : x = 0
  simp [xe0, f0]
  have xneg: x <0 := by push_neg at xpos xe0; exact lt_of_le_of_ne xpos xe0
  have : f x = -(f (-1)) * x := by apply cla4; assumption
  simp [hm11] at this; assumption

  right;right;right;right;
  intro x;
  by_cases xpos : 0 < x
  have : |x| = x := by apply abs_of_pos;assumption
  rw [this];
  have : f x = f 1 * x := by apply cla3; linarith
  rw [h1m1] at this; field_simp at this; assumption
  by_cases xe0 : x = 0
  simp [xe0, f0]
  have xneg: x <0 := by push_neg at xpos xe0; exact lt_of_le_of_ne xpos xe0
  have : |x| = -x := by apply abs_of_neg;exact xneg
  rw [this]
  have : f x = -(f (-1)) * x := by apply cla4; assumption
  simp [hm1m1] at this; ring_nf; assumption

  

  --From right ro left. Simple verification.
  intro h
  rcases h with h | h | h | h | h
  intro x y; simp [h]
  intro x y; simp [h]; ring
  intro x y; simp [h]; ring
  intro x y; simp [h];
  have t1: |x^2+y^2| = x^2 + y^2 := by norm_num; positivity
  have t2: |x*y| = |x| * |y| := by exact abs_mul x y
  rw [t1,t2]; ring
  intro x y; simp [h]
  have t1: |x^2+y^2| = x^2 + y^2 := by norm_num; positivity
  have t2: |x*y| = |x| * |y| := by exact abs_mul x y
  rw [t1,t2]; ring