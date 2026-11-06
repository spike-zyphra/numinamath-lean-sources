import Mathlib
open Polynomial

/- Prove that any real solution of

$$
x^{3}+p x+q=0
$$

satisfies the inequality $4 q x \leq p^{2}$. -/
theorem algebra_605462 {p q : ℝ} (x : ℝ) (hx : (X ^ 3 + C p * X + C q).IsRoot x) : 4 * q * x ≤ p^2 := by
  -- Let $x_{0}$ be a root of the cubic
  -- then $x^{3}+p x+q=\left(x-x_{0}\right)\left(x^{2}+a x+b\right)=$ $x^{3}+\left(a-x_{0}\right) x^{2}+\left(b-a x_{0}\right) x-b x_{0}$.
  have h1 : (X - C x) ∣ (X ^ 3 + C p * X + C q) := by exact dvd_iff_isRoot.mpr hx
  have h2 : ∃ g : Polynomial ℝ, (X ^ 3 + C p * X + C q) = (X - C x) * g := by exact h1
  rcases h2 with ⟨g,hg⟩
  have h3 : (X ^ 3 + C p * X + C q).natDegree ≤ 3 := by
    have : (C p * X).natDegree ≤ 1 := by rw [← pow_one X] ;apply Polynomial.natDegree_C_mul_X_pow_le
    apply Polynomial.natDegree_add_le_of_degree_le ;apply Polynomial.natDegree_add_le_of_degree_le
    simp ;linarith ;simp
  have h4 : g.natDegree ≤ 2 := by
    by_cases h : g = 0
    · rw [h] ;simp
    rw [hg,Polynomial.natDegree_mul] at h3 ;simp at h3 ;exact Nat.le_of_add_le_add_left h3
    exact X_sub_C_ne_zero x ;exact h
  have h5 : ∃ a b c :ℝ , g = (C a) * X ^ 2 + (C b) * X + C c := by
    use (g.coeff 2) ;use (g.coeff 1) ;use (g.coeff 0)
    apply (Polynomial.ext_iff_natDegree_le h4 ?_).mpr
    intro i hi
    apply Nat.le_or_eq_of_le_succ at hi ;rcases hi with hi |hi
    apply Nat.le_one_iff_eq_zero_or_eq_one.mp at hi ;rcases hi with hi |hi
    simp [hi] ;simp [hi] ;simp [hi]
    apply Polynomial.natDegree_add_le_of_degree_le ;apply Polynomial.natDegree_add_le_of_degree_le
    apply Polynomial.natDegree_C_mul_X_pow_le
    have : (C (g.coeff 1) * X).natDegree ≤ 1 := by rw [← pow_one X] ;apply Polynomial.natDegree_C_mul_X_pow_le
    linarith ;simp
  rcases h5 with ⟨a,b,c,hg'⟩
  have hg'' : ((X - C x) * g) = C a * X ^ 3 + C (b - a * x) * X ^ 2 + C (c - b * x) * X + C (- c * x) := by simp [hg',Polynomial.C_mul] ;ring_nf
  have : (C (b - a * x) * X ^ 2).coeff 3 = 0 := by rw [Polynomial.coeff_C_mul_X_pow] ;simp
  have this' : (C (b - a * x) * X ^ 2).coeff 2 = b - a * x := by rw [Polynomial.coeff_C_mul_X_pow] ;simp
  have this'' : (C (b - a * x) * X ^ 2).coeff 1 = 0 := by rw [Polynomial.coeff_C_mul_X_pow] ;simp
  have coeff3 : ((X - C x) * g).coeff 3 = a := by rw [hg'',coeff_add,coeff_add,coeff_add,this] ;simp
  have coeff2 : ((X - C x) * g).coeff 2 = b - a * x := by rw [hg'',coeff_add,coeff_add,coeff_add,this'] ;simp
  have coeff1 : ((X - C x) * g).coeff 1 = c - b * x := by rw [hg'',coeff_add,coeff_add,coeff_add,this''] ;simp
  have coeff0 : ((X - C x) * g).coeff 0 = - c * x := by rw [hg''] ;simp
  -- So $a=x_{0}, p=b-a x_{0}=b-x_{0}^{2},-q=b x_{0}$.
  rw [← hg] at coeff3 ;simp at coeff3
  rw [← hg,← coeff3] at coeff2 ;simp at coeff2
  symm at coeff2 ;apply sub_eq_iff_eq_add.mp at coeff2 ;rw [zero_add] at coeff2
  rw [← hg,coeff2] at coeff1 ;simp at coeff1
  rw [← hg] at coeff0 ;simp at coeff0
  -- Hence $p^{2}=b^{2}-2 b x_{0}^{2}+x_{0}^{4}$.
  have hpsq : p ^ 2 = c ^ 2 - 2 * c * x ^ 2 + x ^ 4 := by rw[coeff1] ;ring
  -- Also $4 x_{0} q=-4 x_{0}^{2} b$.
  have h4xq : 4 * q * x = - 4 * x ^ 2 * c := by rw [coeff0] ;ring
  -- So $p^{2}-4 x_{0} q=b^{2}+2 b x_{0}^{2}+x_{0}^{4}=\left(b+x_{0}^{2}\right)^{2} \geq 0$.
  have h : p ^ 2 - 4 * q * x = (c + x ^ 2) ^ 2 := by rw [hpsq,h4xq] ;ring
  have h' : p ^ 2 - 4 * q * x ≥ 0 := by rw [h] ;exact sq_nonneg (c + x ^ 2)
  exact sub_nonneg.mp h'
  