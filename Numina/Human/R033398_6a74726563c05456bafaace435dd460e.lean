import Mathlib

/- Soient $a$ et $b$ deux réels. Supposons que $2 a+a^{2}=2 b+b^{2}$. Montrer que si $a$ est un entier (pas forcément positif), alors b est aussi un entier. -/
theorem algebra_607159 {a b : ℝ} (h : 2 * a + a ^ 2 = 2 * b + b ^ 2) (ha : ∃ m : ℤ, a = m) :
    ∃ n : ℤ, b = n := by
  obtain ⟨m, ha⟩ := ha
  -- On réécrit l'égalité $$ \begin{gathered} 2 a-2 b=b^{2}-a^{2} \ 2(a-b)=-(a+b)(a-b) \end{gathered} $$
  have h : 2 * (a - b) = (-a - b) * (a - b) := by linarith
  simp at h
  -- Alors soit $\mathrm{b}=\mathrm{a}$, et alors b est un entier,
  cases h with
  | inr h =>
    use m
    linarith
  | inl h =>
    -- soit $$ 2=-a-b $$ d'où $$ \mathrm{b}=-2-\mathrm{a} $$
    have h : b = -2 - a := by linarith
    -- et $b$ est encore un entier.
    use -2 - m
    simp [h, ha]
