import Mathlib

open Polynomial

/- Example 6 Given that $f(x)$ is an $n(n>0)$ degree polynomial of $x$, and for any real number $x$, it satisfies:
$$
8 f\left(x^{3}\right)-x^{6} f(2 x)-2 f\left(x^{2}\right)+12=0
$$

Find $f(x)$ -/
theorem algebra_278880 {f : Polynomial ℝ} (hdeg : 0 < f.degree)
    (hf : ∀ x : ℝ, 8 * f.eval (x ^ 3) - x ^ 6 * f.eval (2 * x) - 2 * f.eval (x ^ 2) + 12 = 0) :
    f = X ^ 3 - 2 := by
  rw [← natDegree_pos_iff_degree_pos] at hdeg
  set n := f.natDegree with n_def
  /- We replace `hf` by an equivalent condition, in the form of polynomial equality,
    rather than pointwise equality. -/
  replace hf : 8 * f.comp (X ^ 3) - X ^ 6 * f.comp (2 * X) - 2 * f.comp (X ^ 2) + 12 = 0 := by
    apply Polynomial.funext
    simpa
  /- Prove that the degree of `f` is $3$. -/
  have deg_eq : n = 3 := by
    /- It's sufficient to prove that $3n = n + 6$. -/
    suffices 3 * n = n + 6 by omega
    /- Rearrange terms in the equality. -/
    have : 8 * f.comp (X ^ 3) - 2 * f.comp (X ^ 2) = X ^ 6 * f.comp (2 * X) - 12 := by
      rw [← sub_eq_zero, ← hf]
      abel
    apply_fun natDegree at this
    rw [natDegree_sub_eq_left_of_natDegree_lt, natDegree_sub_eq_left_of_natDegree_lt] at this
    · convert this using 1
      · /- The degree of $8 f(x^3)$ is $3n$. -/
        symm
        compute_degree <;> simp [natDegree_comp, mul_comm]
        intro h
        apply_fun natDegree at h
        simp [natDegree_comp] at h
        omega
      · /- The degree of $x^6 f(2x)$ is $2n$. -/
        symm
        compute_degree <;> simp [natDegree_comp, add_comm]
        intro h
        apply_fun natDegree at h
        simp [natDegree_comp] at h
        omega
    · /- The degree of $12$ is less than the degree of $x^6 f(2x)$. -/
      rw [Polynomial.natDegree_mul]
      · simp
      · simp
      · intro h
        apply_fun natDegree at h
        simp [natDegree_comp] at h
        omega
    · /- The degree of $2 f(x^2)$ is less than the degree of $8 f(x^3)$. -/
      rw [show 2 = C (2 : ℝ) from rfl, show 8 = C (8 : ℝ) from rfl]
      simp [natDegree_comp, natDegree_C_mul]
      omega
  /- We can rewrite $f$ as $a_3 x^3 + a_2 x^2 + a_1 x + a_0$. -/
  have f_eq := f.as_sum_range_C_mul_X_pow
  simp [← n_def, deg_eq, Finset.sum_range_succ_comm] at f_eq
  set a₀ := f.coeff 0
  set a₁ := f.coeff 1
  set a₂ := f.coeff 2
  set a₃ := f.coeff 3
  /- By comparing the $x^0$-coefficient, we can prove that $a_0 = -2$. -/
  have a₀_eq : a₀ = -2 := by
    apply_fun (coeff · 0) at hf
    simp [f_eq] at hf
    ring_nf at hf
    simp [Polynomial.coeff_C] at hf
    linarith
  /- By comparing the $x^7$-coefficient, we can prove that $a_1 = 0$. -/
  have a₁_eq : a₁ = 0 := by
    apply_fun (coeff · 7) at hf
    simp [f_eq] at hf
    ring_nf at hf
    simpa using hf
  /- By comparing the $x^8$-coefficient, we can prove that $a_2 = 0$. -/
  have a₂_eq : a₂ = 0 := by
    apply_fun (coeff · 8) at hf
    simp [f_eq] at hf
    ring_nf at hf
    simpa using hf
  /- By comparing the $x^6$-coefficient and substituting the value of $a_0$ and $a_2$,
    we can prove that $a_3 = 1$. -/
  have a₃_eq : a₃ = 1 := by
    apply_fun (coeff · 6) at hf
    simp [f_eq, a₀_eq, a₂_eq] at hf
    ring_nf at hf
    simp at hf
    linarith
  /- Then we can prove the result. -/
  rw [a₀_eq, a₁_eq, a₂_eq, a₃_eq] at f_eq
  simp [f_eq, show 2 = C (2 : ℝ) from rfl]
  abel
