import Mathlib
open Polynomial

/- 1. Let $g(x)=a x^{2}+b x+c$ divide $f(x)=x^{3}+p x^{2}+q x+r$, where $a b c \neq 0$, then $\frac{a p-b}{a}=\frac{a q-c}{b}=\frac{a r}{c}$. -/
theorem algebra_195903 {K : Type*} [Field K] {a b c p q r : K} {f g : Polynomial K} (hf : f = X^3 + C p * X^2 + C q * X + C r)
    (hg : g = C a * X^2 + C b * X + C c) (habc : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0) (hfg : g ∣ f) :
    (a * p - b) / a = (a * q - c) / b ∧ (a * q - c) / b = a * r / c := by
    rcases hfg with ⟨h, hfgh⟩

    -- deg f = deg g + deg h, deg f = 3, deg g = 2 => deg h = 1
    have h_deg : natDegree h = 1
    · have f_deg : natDegree f = 3
      · rw [hf, add_assoc, add_assoc (X^3), natDegree_add_eq_left_of_natDegree_lt]
        all_goals simp only [natDegree_pow, natDegree_X, mul_one]
        calc
          (C p * X ^ 2 + (C q * X + C r)).natDegree
          ≤ max (C p * X ^ 2).natDegree (C q * X + C r).natDegree := by exact natDegree_add_le _ _
          _ ≤ max (C p * X ^ 2).natDegree (max (C q * X).natDegree (C r).natDegree) := by apply max_le_max_left; exact natDegree_add_le (C q * X) (C r)
          _ ≤ max 2 (max (C q * X).natDegree (C r).natDegree) := by apply max_le_max_right; exact natDegree_C_mul_X_pow_le p 2
          _ ≤ max 2 (max 1 0) := by apply max_le_max_left; simp only [natDegree_C, zero_le, sup_of_le_left]; rw [←pow_one X]; exact natDegree_C_mul_X_pow_le q 1
          _ < 3 := by simp only [zero_le, sup_of_le_left, Nat.one_le_ofNat, Nat.lt_add_one]
      have f_nz : f ≠ 0 := by rw [hf]; intro hf0; have := congr_arg (fun t => coeff t 3) hf0; simp at this
      have g_nz : g ≠ 0 := by rw [hg]; intro hg0; have := congr_arg (fun t => coeff t 2) hg0; simp at this; exact habc.left this
      have h_nz : h ≠ 0 := by rw [←mul_ne_zero_iff_left g_nz, ←hfgh]; exact f_nz
      have g_deg : natDegree g = 2
      · rw [hg, add_assoc, natDegree_add_eq_left_of_natDegree_lt]
        all_goals rw [natDegree_C_mul_X_pow _ _ habc.left]
        rw [natDegree_add_C, ←pow_one X]
        calc
          (C b * X^1).natDegree ≤ 1 := natDegree_C_mul_X_pow_le b 1
          _ < 2 := Nat.one_lt_two
      have deg_add := natDegree_mul g_nz h_nz
      rw [←hfgh, f_deg, g_deg] at deg_add
      exact (Nat.add_left_cancel deg_add).symm
    -- deg h = 1, so we can write h = d * X + e
    rw [eq_X_add_C_of_natDegree_le_one h_deg.le] at hfgh
    rw [hf, hg] at hfgh
    have h_collect : (C a * X^2 + C b * X + C c) * (C (h.coeff 1) * X + C (h.coeff 0)) = C (a * h.coeff 1) * X^3 + C (b * h.coeff 1 + a * h.coeff 0) * X^2 + C (b * h.coeff 0 + c * h.coeff 1) * X + C (c * h.coeff 0) := by calc
      _ = C a * C (h.coeff 1) * X^3 + (C b * C (h.coeff 1) + C a * C (h.coeff 0)) * X^2 + (C b * C (h.coeff 0) + C c * C (h.coeff 1)) * X + C c * C (h.coeff 0) := by ring
      _ = C (a * h.coeff 1) * X^3 + C (b * h.coeff 1 + a * h.coeff 0) * X^2 + C (b * h.coeff 0 + c * h.coeff 1) * X + C (c * h.coeff 0) := by rw [←C_mul, ←C_mul, ←C_mul, ←C_mul, ←C_mul, ←C_mul, ←C_add, ←C_add]
    rw [h_collect] at hfgh

    -- equate coefficients of X^3
    have eq3 := congr_arg (fun t => coeff t 3) hfgh
    simp only [coeff_add, coeff_C_mul, coeff_X_pow] at eq3
    rw [coeff_X_of_ne_one (by linarith)] at eq3
    simp at eq3
    -- solve for h.coeff 1
    have h_coef1 : h.coeff 1 = 1/a := eq_one_div_of_mul_eq_one_right eq3.symm

    -- equate coefficients of X^2
    have eq2 := congr_arg (fun t => coeff t 2) hfgh
    simp only [coeff_add, coeff_C_mul, coeff_X_pow] at eq2
    rw [coeff_X_of_ne_one (by linarith)] at eq2
    simp at eq2
    rw [h_coef1] at eq2
    -- solve for h.coeff 0
    have res0 : a * h.coeff 0 = (a * p - b) / a := by rw [eq2]; field_simp [habc.left]

    -- equate coefficients of X
    have eq1 := congr_arg (fun t => coeff t 1) hfgh
    simp only [coeff_add, coeff_C_mul, coeff_X_pow] at eq1
    simp at eq1
    rw [h_coef1] at eq1
    have res1 : a * h.coeff 0 = (a * q - c) / b := by rw [eq1]; field_simp [habc.left, habc.right.left]; ring

    -- equate constants
    have eq0 := congr_arg (fun t => coeff t 0) hfgh
    simp at eq0
    have res2 : h.coeff 0 = r / c := by field_simp [habc.right.right]; rw [eq0, mul_comm]

    constructor
    · rw [←res0, ←res1]
    · rw [←res1, res2, mul_div_assoc']