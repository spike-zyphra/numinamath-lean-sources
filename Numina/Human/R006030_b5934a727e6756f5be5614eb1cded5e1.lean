import Mathlib

open Real

namespace calculus_611204

noncomputable def seq (n : ℕ) : ℝ → ℝ :=
  match n with 
  -- Define $f_{0}(x)=x$ and $f_{n}(x)=\cos f_{n-1}(x)$ for $n \geq 0$.
  | 0 => fun x ↦ x
  | n + 1 => fun x ↦ cos (seq n x)

lemma seq_succ (n : ℕ) :
    seq (n + 1) = cos ∘ (seq n) := rfl

lemma differentiable_seq (n : ℕ) :
    Differentiable ℝ (seq n) := by
  induction n with
  | zero => exact differentiable_id
  | succ n ih =>
      rw [seq_succ]
      apply Differentiable.comp
      · exact differentiable_cos
      · exact ih

lemma seq_eq (a : ℝ) (ha : cos a = a) (n : ℕ) :
    seq n a = a := by
  induction n with
  -- We will show by induction that $f_{n}(a)=a$ 
  | zero => simp [seq]
  -- The case $n=0$ is clear. Then $f_{n}(a)=\cos f_{n-1}(a)=\cos a=a$, 
  | succ n ih =>
    rw [seq_succ]
    simp only [Function.comp_apply]
    rw [ih, ha]

theorem seq_deriv (a : ℝ) (ha : cos a = a) (n : ℕ) :
    deriv (seq n) a = (- sin a) ^ n := by
  -- and $f_{n}^{\prime}(a)=(-\sin a)^{n}$ for all $n$.
  induction n with
  | zero => simp [seq]
  | succ n ih =>
      rw [seq_succ]
      rw [deriv_comp]
  -- and $$ f_{n}^{\prime}(a)=f_{n-1}^{\prime}(a) \cdot\left(-\sin f_{n-1}(a)\right)
  -- =(-\sin a)^{n-1} \cdot(-\sin a)=(-\sin a)^{n} $$ by induction.
      · simp only [deriv_cos', neg_mul]
        rw [ih, seq_eq a ha n]
        ring
      · apply differentiable_cos
      · exact differentiable_seq n a

end calculus_611204

open calculus_611204

/- Let $f(x)=\cos (\cos (\cos (\cos (\cos (\cos (\cos (\cos x)))))))$,
and suppose that the number $a$ satisfies the equation $a=\cos a$.
Express $f^{\prime}(a)$ as a polynomial in $a$. -/
theorem calculus_611204 (f : ℝ → ℝ) (hf : f = cos ∘ cos ∘ cos ∘ cos ∘ cos ∘ cos ∘ cos ∘ cos)
    (a : ℝ) (ha : cos a = a) : deriv f a = a ^ 8 - 4 * a ^ 6 + 6 * a ^ 4 - 4 * a ^ 2 + 1 := by
  have hf : f = seq 8 := by
    ext x
    simp only [hf, Function.comp_apply, seq]
  -- Now, $f(x)=f_{8}(x)$,
  calc
    _ = (sin a ^ 2) ^ 4 := by rw [hf, seq_deriv a ha 8] ; ring
   --  so $f^{\prime}(a)=(-\sin a)^{8}=\sin ^{8} a$.
    _ = (1 - (cos a) ^ 2) ^ 4 := by rw [sin_sq]
    -- Now, $f(x)=f_{8}(x)$, so $f^{\prime}(a)=(-\sin a)^{8}=\sin ^{8} a$.
    -- But $\sin ^{2} a=1-$ $\cos ^{2} a=1-a^{2}$,
    -- so $f^{\prime}(a)=\left(1-a^{2}\right)^{4}=a^{8}-4 a^{6}+6 a^{4}-4 a^{2}+1$.-/
    _ = (1 - a ^ 2) ^ 4 := by rw [ha]
    _ = _ := by ring


