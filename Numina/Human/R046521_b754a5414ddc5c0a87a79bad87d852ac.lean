import Mathlib
open Polynomial

/- . Find all polynomials $p(x)$ with real coefficients such that

$$
p(a+b-2 c)+p(b+c-2 a)+p(c+a-2 b)=3 p(a-b)+3 p(b-c)+3 p(c-a)
$$

for all $a, b, c \in \mathbb{R}$. -/
theorem algebra_290578 : {p : Polynomial ℝ | ∀ a b c, p.eval (a + b - 2 * c) + p.eval (b + c - 2 * a) + p.eval (c + a - 2 * b) = 3 * p.eval (a - b) + 3 * p.eval (b - c) + 3 * p.eval (c - a)} =
  {p : Polynomial ℝ | ∀ m :ℕ ,m ≠ 1 ∧ m≠ 2 → p.coeff m = 0} := by
  ext p ;simp ;constructor
  intro hp
  -- For $a=b=c$, we have $3 p(0)=9 p(0)$, hence $p(0)=0$.
  have h1 := hp 0 0 0
  ring_nf at h1 ;simp at h1
  -- Now set $b=c=0$, then we have$$ p(a)+p(-2 a)+p(a)=3 p(a)+3 p(-a) $$for all $a \in \mathbb{R}$.
  have h2 : ∀ a, p.eval (-2*a) = p.eval a + 3 * p.eval (-a) := by
    intro a
    have h2 := hp a 0 0
    simp [h1] at h2 ; ring_nf at h2
    replace h2 : eval (-(a * 2)) p = eval a p * 3 + eval (-a) p * 3 - eval a p * 2 := by exact eq_sub_of_add_eq' h2
    ring_nf at h2 ;ring_nf ;exact h2
  -- So we find a polynomial equation $$ p(-2 x)=p(x)+3 p(-x) \text {. } $$
  have heq : p.comp ((C (-2 :ℝ)) * X) = p + 3 * p.comp ((C (-1 :ℝ)) * X) := by
    apply Polynomial.funext
    intro a ;simp ;specialize h2 a ;rw [← h2] ;simp
  -- Note that the zero polynomial is a solution to this equation.
  by_cases h3 : p = 0
  · intro m hm1 hm2;simp [h3]
  -- Now suppose that $p$ is not the zero polynomial, and let $n \geq 0$ be the degree of $p$.
  let n := p.degree
  have h4 : 0 ≤ n := by simp [n] ; exact zero_le_degree_iff.mpr h3
  -- Let $a_{n} \neq 0$ be the coefficient of $x^{n}$ in $p(x)$.
  let a m := p.coeff m
  --  At the left-hand side of (1), the coefficient of $x^{n}$ is $(-2)^{n} \cdot a_{n}$,
  have h5 : ∀ m,(p.comp ((C (-2 :ℝ)) * X)).coeff m = (- 2) ^ m * a m := by
    intro m ;rw [Polynomial.comp_C_mul_X_coeff] ;simp [a] ;ring
  -- while at the right-hand side the coefficient of $x^{n}$ is $a_{n}+3 \cdot(-1)^{n} \cdot a_{n}$.
  have h6 : ∀ m, (p + 3 * p.comp ((C (-1 :ℝ)) * X)).coeff m = a m + 3 * (-1) ^ m * a m := by
    intro m ;simp
    have : (p.comp (-X)).coeff m = (p.comp ((C (-1 :ℝ))*X)).coeff m := by simp
    rw [this,Polynomial.comp_C_mul_X_coeff] ;ring
  --  Hence $(-2)^{n}=1+3 \cdot(-1)^{n}$.
  have heq' : ∀ m, (p.comp ((C (-2 :ℝ)) * X)).coeff m = (p + 3 * p.comp ((C (-1 :ℝ)) * X)).coeff m := by
    intro m ;rw [heq]
  have heq'' : ∀ m , a m ≠ 0 → (- 2:ℝ ) ^ m = 1 + 3 * (-1) ^ m := by
    intro m hm
    specialize heq' m
    rw [h5,h6] at heq'
    nth_rewrite 2 [← one_mul (a m)] at heq'
    rw [← add_mul] at heq'
    apply mul_right_cancel₀ hm at heq' ;rw [heq']
  -- For $n$ even, we find $2^{n}=4$, so $n=2$,
  intro m hm1 hm2
  by_cases hm : Even m
  by_cases hm' : a m ≠ 0
  · specialize heq'' m hm'
    rcases hm with ⟨k,hk⟩
    rw [hk] at heq'' ;simp [← two_mul,pow_mul] at heq'' ;norm_num at heq''
    have : k = 1 := by
      by_contra! h
      by_cases h' : k = 0
      · simp [h'] at heq''
      have : 1 < k := by refine Nat.one_lt_iff_ne_zero_and_ne_one.mpr ?_ ;simp [h,h']
      have : (4:ℝ) ^ 1 < 4 ^ k := by refine pow_lt_pow_right₀ ?_ this ;simp
      linarith
    simp [this] at hk ;exact False.elim (hm2 hk)
  simp [a] at hm' ;exact hm'
  -- and for $n$ odd, we find $-2^{n}=-2$, so $n=1$.
  simp at hm
  by_cases hm' : a m ≠ 0
  · specialize heq'' m hm'
    rcases hm with ⟨k,hk⟩
    rw [hk] at heq'' ;norm_num at heq'' ;rw [← hk] at heq''
    replace heq'' : abs ((- 2 :ℝ) ^ m) = abs (- 2) := by rw [heq'']
    simp at heq''
    have : m = 1 := by
      by_contra! h
      by_cases h' : m = 0
      · simp [h'] at hk
      have : 1 < m := by refine Nat.one_lt_iff_ne_zero_and_ne_one.mpr ?_ ;simp [h,h']
      have : (2:ℝ) ^ 1 < 2 ^ m := by refine pow_lt_pow_right₀ ?_ this ;simp
      linarith
    exact False.elim (hm1 this)
  simp [a] at hm' ;exact hm'
  --  As we already know that $p(0)=0$, we must have $p(x)=a_{2} x^{2}+a_{1} x$, where $a_{1}$ and $a_{2}$ are real numbers (possibly zero).
  intro hm
  have : ∃ a₁ : ℝ ,∃  a₂ :ℝ , p = C a₂ * X ^ 2 + C a₁ * X := by
    use p.coeff 1,p.coeff 2
    ext x
    by_cases hx : (¬ x = 1) ∧ (¬ x = 2)
    · specialize hm x hx.1 hx.2
      simp [hm]
      by_cases hx' : x = 0
      · simp [hx']
      simp [hx] ;right ;refine coeff_X_of_ne_one ?_ ;simp [hx]
    simp at hx
    by_cases hx' : x = 1
    · simp [hx']
    apply hx at hx' ;simp [hx']
  -- The polynomial $p(x)=x$ is a solution to our problem, as $$ (a+b-2 c)+(b+c-2 a)+(c+a-2 b)=0=3(a-b)+3(b-c)+3(c-a) $$ for all $a, b, c \in \mathbb{R}$.
  have hx : ∀ (a b c : ℝ), eval (a + b - 2 * c) X + eval (b + c - 2 * a) X + eval (c + a - 2 * b) X =
    3 * eval (a - b) X + 3 * eval (b - c) X + 3 * eval (c - a) X := by
    intro a b c ;simp ;ring
  -- Also, $p(x)=x^{2}$ is a solution, since
  -- $$ \begin{aligned} (a+b-2 c)^{2}+(b+c-2 a)^{2}+(c+a-2 b)^{2} & =6\left(a^{2}+b^{2}+c^{2}\right)-6(a b+b c+c a) \ & =3(a-b)^{2}+3(b-c)^{2}+3(c-a)^{2} \end{aligned} $$
  -- for all $a, b, c \in \mathbb{R}$.
  have hx2 : ∀ (a b c : ℝ), eval (a + b - 2 * c) X^2 + eval (b + c - 2 * a) X^2 + eval (c + a - 2 * b) X^2 =
    3 * eval (a - b) X^2 + 3 * eval (b - c) X^2 + 3 * eval (c - a) X^2 := by
    intro a b c ;simp ;ring
  -- Now note that if $p(x)$ is a solution to our problem, then so is $\lambda p(x)$ for all $\lambda \in \mathbb{R}$.
  -- Also, if $p(x)$ and $q(x)$ are both solutions, then so is $p(x)+q(x)$.
  -- We conclude that for all real numbers $a_{2}$ and $a_{1}$ the polynomial $a_{2} x^{2}+a_{1} x$ is a solution.
  --  Since we have already shown that there can be no other solutions, these are the only solutions.
  intro a b c
  rcases this with ⟨a₁,a₂,h⟩
  rw [h] ;simp ;ring
  