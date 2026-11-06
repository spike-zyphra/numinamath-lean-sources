import Mathlib

/-
  Given a finite sequence $S=(a_1,a_2,\ldots ,a_n)$ of $n$ real numbers, let $A(S)$ be the
  sequence $\left(\frac{a_1+a_2}{2},\frac{a_2+a_3}{2},\ldots ,\frac{a_{n-1}+a_n}{2}\right)$ of $n-1$
  real numbers. Define $A^1(S)=A(S)$ and, for each integer $m$, $2\le m\le n-1$, define
  $A^m(S)=A(A^{m-1}(S))$. Suppose $x>0$, and let $S=(1,x,x^2,\ldots ,x^{100})$. If
  $A^{100}(S)=(1/2^{50})$, then what is $x$? $\mathrm{(A) \ } 1-\frac{\sqrt{2}}{2}\qquad \mathrm{(B)
  \ } \sqrt{2}-1\qquad \mathrm{(C) \ } \frac{1}{2}\qquad \mathrm{(D) \ } 2-\sqrt{2}\qquad
  \mathrm{(E) \ }  \frac{\sqrt{2}}{2}$
-/

open Real

/- Definition of $A(S)$ -/
noncomputable def A (S : ℕ → ℝ) : ℕ → ℝ := fun i => (S i + S (i + 1)) / 2

/- Definition of $A^m(S)$ -/
noncomputable def A_iter (m : ℕ) (S : ℕ → ℝ) : ℕ → ℝ :=
  match m with
  | 0 => S
  | m + 1 => A (A_iter m S)

theorem algebra_1166 (x : ℝ) (hx : x > 0) :
    let S := fun (x : ℝ) => (x ^ ·);
    A_iter 100 (S x) 0 = 1 / 2 ^ 50 →
    x = √2 - 1 := by
  intro S h
  /- In general,
  $A^n(S)=\left(\frac{(x+1)^n}{2^n},\frac{x(x+1)^n}{2^n},...,\frac{x^{100-n}(x+1)^n}{2^n}\right)$
  such that $A^n(s)$ has $101-n$ terms. -/
  have A_iter_value : ∀ (n : ℕ), A_iter n (S x) = fun i => x ^ i * (x + 1) ^ n / 2 ^ n := by {
    intro n
    induction n with
    | zero =>
      funext i
      simp [A_iter]
    | succ n ih =>
      funext i
      simp only [A_iter]
      rw [ih]
      simp only [A]
      ring
  }
  /- Specifically, $A^{100}(S)=\frac{(x+1)^{100}}{2^{100}}$. -/
  specialize A_iter_value 100
  apply funext_iff.1 at A_iter_value
  specialize A_iter_value 0
  rw [pow_zero, one_mul] at A_iter_value
  /- To find x, we need only solve the equation $\frac{(x+1)^{100}}{2^{100}}=\frac{1}{2^{50}}$. -/
  have eq1 : 1 / 2 ^ 50 = (x + 1) ^ 100 / 2 ^ 100 := by rw [← h, ← A_iter_value]
  /- so $(1+x)^{100}=2^{50}$, -/
  have eq2 : (x + 1) ^ 100 = 2 ^ 50 := by
    calc (x + 1) ^ 100 = (x + 1) ^ 100 / 2 ^ 100 * 2 ^ 100 := by field_simp
                     _ = 1 / 2 ^ 50  * 2 ^ 100 := by rw [← eq1]
                     _ = 2 ^ 50 := by ring
  /- and because $x>0$, we have $x=\boxed{\sqrt{2}-1}$. -/
  calc x = (x + 1) - 1 := by ring
       _ = ((x + 1) ^ 100) ^ (↑(100 : ℕ) : ℝ)⁻¹ - 1 := by rw [pow_rpow_inv_natCast] <;> linarith
       _ = (2 ^ 50) ^ ((1 / 100) : ℝ) - 1 := by rw [eq2]; field_simp
       _ = 2 ^ ((50 * (1 / 100)) : ℝ) - 1 := by rw [← rpow_natCast, ← rpow_mul _ _]; simp; linarith
       _ = 2 ^ ((1 / 2) : ℝ) - 1 := by norm_num
       _ = √2 - 1 := by rw [← sqrt_eq_rpow]