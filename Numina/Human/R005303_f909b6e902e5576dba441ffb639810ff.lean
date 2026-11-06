import Mathlib

/- Bepaal het grootste reële getal $M$ zodanig dat voor elke oneindige rij $x_{0}, x_{1}, x_{2}, \ldots$ van reële getallen die voldoet aan
a) $x_{0}=1$ en $x_{1}=3$,
b) $x_{0}+x_{1}+\cdots+x_{n-1} \geq 3 x_{n}-x_{n+1}$,
geldt dat

$$
\frac{x_{n+1}}{x_{n}}>M
$$

voor alle $n \geq 0$. -/
theorem algebra_607473  :
    {f : ℝ → ℝ | ∀ x : ℝ, ∀ y : ℝ, f ((x + y) / 3) = (f x + f y) / 2 } = {f | ∃ c, f = λ _ ↦ c} := by
  ext f
  simp
  constructor
  . intro hf
    -- Let us first note that the function $g:x ↦ f(x)−f(0)$ is also a solution of the functional equation.
    let g := λ x ↦ f x - f 0
    have hg (x: ℝ): f x = g x + f 0 := by simp [g]
    have hg_0 : g 0 = 0 := by simp [g]

    conv at hf =>
      intro x y
      rw [hg, hg x, hg y, <-sub_eq_zero]
      rw [show g ((x + y) / 3) + f 0 - (g x + f 0 + (g y + f 0)) / 2 = g ((x + y) / 3) - (g x + g y ) / 2 by ring]
      rw [sub_eq_zero]
      rfl

    -- We can now prove that $g(3x) = g(2x)$ for all $x$ by setting $(3x, 3x)$ in `hf`
    have h1 (x: ℝ): g (2 * x) = g (3 * x) := by
      specialize hf (3 * x) (3 * x)
      simp at hf
      rw [<-hf]
      ring_nf

    -- We can now prove that $g (3x) = 2g(x)$ for all $x$ by setting $(3x, 0)$ in `hf`
    have h2 (x: ℝ): g (3 * x) = 2 * g x := by
      specialize hf (3 * x) 0
      simp [hg_0] at hf
      linear_combination -2 * hf
    -- Combining the two results, we have $g(2x) = 2g(x)$ for all $x$
    have h3 (x: ℝ): g (2 * x) = 2 * g x := by rw [h1, h2]

    -- We can now prove that $g(x) = g(2x)$ for all $x$ by setting $(x, 2x)$ in `hf`
    have h4 (x: ℝ): g x = g (2 * x) := by
      specialize hf x (2 * x)
      ring_nf at hf
      ring_nf
      linear_combination 2 * hf
    -- Since we have $g(x) = g(2x)$ and $g(2x) = 2g(x)$, we have $g(x) = 0$ for all $x$
    have h5 (x: ℝ): g x = 0 := by
      specialize h3 (x/2)
      specialize h4 (x/2)
      rw [h4] at h3
      ring_nf at h3
      ring_nf
      linear_combination -h3
    -- so the const is $f(0)$
    use f 0
    ext x
    rw [<-sub_eq_zero]
    exact h5 x
  -- the const function is a solution
  . intro ⟨c, hf⟩
    rw [hf]
    simp
