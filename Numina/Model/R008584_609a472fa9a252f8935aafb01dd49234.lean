import Mathlib

theorem Algebra_8432 :
    {f : ℝ → ℝ | ∀ x y, f (f x + y) = 2 * x + f (f y - x)} = {f | ∃ c, f = fun x => x + c} := by 
  ext f
  simp only [Set.mem_setOf_eq]
  apply Iff.intro
  · -- Forward implication: if f satisfies the equation, then f(x) = x + c for some c
    intro hf
    -- 15. We observe first that $f$ is surjective. 
    have fSurj : f.Surjective := by {
      intro z
      have crux : ∀ x, f (f (- f x) - x) = f 0 - 2 * x := by
        intro x
        specialize hf x (- f x)
        simp at hf
        linarith
      have : ∃ x, f 0 - 2 * x = z := by
        use (f 0 - z) / 2
        ring
      match this with
      | ⟨x, hx⟩ => 
        use (f (-f x) - x)
        rw [crux]
        linarith
    }
    -- In particular, there exists $x_{0}$ for which $f\left(x_{0}\right)=0$.
    have : ∃ x₀, f x₀ = 0 := fSurj 0
    match this with
    | ⟨x₀, hx0⟩ => 
      -- We show c := x₀ works
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
      | ⟨y, hy⟩ => 
        rw [← hy]
        have eq := hf x₀ y
        simp [hx0] at eq
        linarith
  · -- Reverse implication: if f(x) = x + c for some c, then it satisfies the equation
    intro hf
    rcases hf with ⟨c, rfl⟩
    intro x y 
    simp [add_assoc]
    <;> ring