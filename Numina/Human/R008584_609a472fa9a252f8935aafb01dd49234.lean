import Mathlib

theorem Algebra_8432 :
    {f : ℝ → ℝ | ∀ x y, f (f x + y) = 2 * x + f (f y - x)} = {f | ∃ c, f = fun x => x + c} := by
  ext f
  simp only [Set.mem_setOf_eq]
  apply Iff.intro
  · intro hf
    -- 15. We observe first that $f$ is surjective. 
    have fSurj : f.Surjective := by {
      -- Indeed, setting $y=-f(x)$ gives $f(f(-f(x))-x)=f(0)-2 x$,
      intro z
      have crux : ∀ x, f (f (- f x) - x) = f 0 - 2 * x := by
        intro x
        specialize hf x (- f x)
        simp at hf
        linarith
      -- where the right-hand expression can take any real value.
      have : ∃ x, f 0 - 2 * x = z := by
        use (f 0 - z) / 2
        ring
      match this with
      | ⟨x, hx⟩ => 
        use (f (-f x) - x)
        rw [crux]
        exact hx
    }
    -- In particular, there exists $x_{0}$ for which $f\left(x_{0}\right)=0$.
    have : ∃ x₀, f x₀ = 0 := fSurj 0
    match this with
    | ⟨x₀, hx0⟩ => {
      -- we show c := x₀ works
      use (-x₀)
      ext z
      -- Since $f$ is surjective, $z$ takes all real values. 
      have : ∃ y, f y - x₀ = z := by 
        have := fSurj (z + x₀)
        match this with
        | ⟨y, hy⟩ => 
          use y
          linarith
      match this with
      | ⟨y, hy⟩ => {
        rw [← hy]
        -- Now setting $x=x_{0}$ in the functional equation yields $f(y)=2 x_{0}+f\left(f(y)-x_{0}\right)$, so we obtain  $$ f(z)=z-x_{0} \quad \text { for } z=f(y)-x_{0} $$  
        specialize hf x₀ y
        simp [hx0] at hf
        linarith
      }
    }
  · intro ⟨c, hc⟩ 
    intro x y
    simp [hc]
    ring