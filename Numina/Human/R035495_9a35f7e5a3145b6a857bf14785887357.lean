import Mathlib

open Finset Real
/- Soit $n \geqslant 3$ et soient $x_{1}, \ldots, x_{n}$ des réels. Montrer que

$$
2\left(x_{1}+\cdots+x_{n}\right)^{2} \leqslant n\left(x_{1}^{2}+\cdots+x_{n}^{2}+x_{1} x_{2}+x_{2} x_{3}+\cdots+x_{n-1} x_{n}+x_{n} x_{1}\right)
$$ -/
theorem inequalities_607366 {n : ℕ} [NeZero n] (_ : 3 ≤ n) (x : Fin n → ℝ) :
  2 * (∑ i, x i) ^ 2 ≤ n * (∑ i, (x i) ^ 2 + ∑ i, x i * x (i + 1)) := by
    -- auxiliary lemma.
    have fin_sum_addOne {n : ℕ} [NeZero n] (f : Fin n → ℝ) :
        ∑ (i : Fin n), f i = ∑ (i : Fin n), f (i + 1) := by
      refine (Function.Bijective.sum_comp ?_ f).symm
      exact AddGroup.addRight_bijective 1
    -- $$ \begin{gathered} \left(x\_{1}+x\_{2}\right)^{2}+\cdots+\left(x\_{n-1}+x\_{n}\right)^{2}+\left(x\_{n}+x\_{1}\right)^{2}=\left(x\_{1}^{2}+2 x\_{1} x\_{2}+x\_{2}^{2}\right)+\cdots+\left(x\_{n-1}^{2}+2 x\_{n-1} x\_{n}+x\_{n}^{2}\right)+\left(x\_{n}^{2}+2 x\_{n} x\_{1}+x\_{1}^{2}\right) \ =2\left(x\_{1}^{2}+\ldots x\_{n}^{2}+x\_{1} x\_{2}+x\_{2} x\_{3}+\cdots+x\_{n-1} x\_{n}+x\_{n} x\_{1}\right) \end{gathered} $$
    have h1 : ∑ i, (x i + x (i + 1))^2 = 2 * (∑ i, (x i) ^ 2 + ∑ i, x i * x (i + 1)) := by
      simp [add_sq, Finset.sum_add_distrib, mul_add, mul_assoc]
      rw [←Finset.mul_sum, ←fin_sum_addOne (fun i => (x i)^2)]
      linarith
    -- $$ 4\left(x\_{1}+\ldots+x\_{n}\right)^{2} \leqslant \mathfrak{n}\left(\left(x\_{1}+x\_{2}\right)^{2}+\left(x\_{2}+x\_{3}\right)^{3}+\ldots+\left(x\_{n-1}+x\_{n}\right)^{2}+\left(x\_{n}+x\_{1}\right)^{2}\right) $$
    have h2 : 4 * (∑ i, x i) ^ 2 ≤ n * ∑ i, (x i + x (i + 1))^2 := calc
      _ = (∑ i, 2 * x i)^2 := by
        simp [←Finset.mul_sum, mul_pow]; norm_num
      _ = (∑ i, (x i + x (i + 1)) )^2 := by
        rw [Finset.sum_add_distrib]
        rw [←fin_sum_addOne, ←Finset.sum_add_distrib]
        simp [two_mul]
      _ ≤ _ := by
        convert @sq_sum_le_card_mul_sum_sq (Fin n) _ _ _ (univ) (fun i => x i + x (i + 1))
        simp
    linarith [h1 ▸ h2 ]
