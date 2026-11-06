import Mathlib

theorem Algebra_610654 (a b c : ℝ) (h1 : a^2 - b*c = 14) (h2 : b^2 -c*a = 14) (h3 : c^2 -a*b = -3) : |a+b+c| = 17/5 := by 
  -- use h1 and h2 to get (a+b+c) = 0 or a = b
  have eq1 : (a^2-b*c) - (b^2-c*a) = 14 - 14 := by linarith
  simp at eq1
  have : (a^2-b*c) - (b^2-c*a) = (a+b+c) * (a-b) := by ring_nf
  rw [this] at eq1
  have : (a+b+c) = 0 ∨ (a-b = 0) := by exact mul_eq_zero.mp eq1
  obtain abceq0 | aeqb := this

  -- it cannot happen that a + b + c = 0
  exfalso
  have ceq : c = -(a+b) := by linarith
  have c2eq: c^2 =  (a+b)^2 := by rw[ceq]; ring_nf
  rw [ceq] at h2; rw [c2eq] at h3; ring_nf at h2; ring_nf at h3; linarith

  -- so a = b
  have aeqb : a = b := by linarith
  rw [← aeqb] at h1
  rw [← aeqb] at h3

  -- substitute a = b in all equations, simplify and solve for a, b, and c
  have a2eq : a^2 = 196/25 := by
    have : a^2 -a * c = a*(a-c) := by ring_nf
    have eq1 : a*(a-c) = 14 := by rw [this] at h1; assumption
    have : c^2 - a*a = -(a+c)*(a-c) := by ring_nf
    rw [this] at h3; 
    have eq2: (a + c) * (a - c) = 3 := by nlinarith
    have : a-c ≠ 0 := by intro hc; rw[hc] at eq1; norm_num at eq1
    have : a = 14 / (a-c):= by field_simp; assumption
    have : (3/14)*a = 3/ (a-c) := by nth_rw 1 [this]; field_simp;
    have : a+c = 3 / (a-c) := by field_simp; assumption
    have : a+c = (3/14)*a := by linarith
    have ceqka: c = (-11/14) * a := by nlinarith

    rw [ceqka] at eq1; ring_nf at eq1; field_simp at eq1; norm_num at eq1;
    nlinarith


  have aeq :(a = 14/5 ∨ a = -14/5) := by 
    have : ((196:ℝ)/25) = (14/5)^2 := by ring_nf
    rw [this] at a2eq
    by_cases ha : 0 ≤ a 
    rw [sq_eq_sq₀] at a2eq; left; assumption; assumption; norm_num
    have : (-a) ^ 2 = a^2 := by ring_nf
    rw [← this] at a2eq
    have : 0 ≤ -a := by linarith
    rw [sq_eq_sq₀] at a2eq; right; linarith; assumption; norm_num
  
  obtain ap | an := aeq
  have beq : b = 14/5 := by linarith
  have ceq : c = -11/5 := by nlinarith
  have abcadd : a + b + c = 17/5 := by nlinarith
  rw [abcadd]; norm_num

  have beq : b = -14/5 := by linarith
  have ceq : c = 11/5 := by nlinarith
  have abcadd : a + b + c = -17/5 := by nlinarith
  rw [abcadd]; norm_num
    