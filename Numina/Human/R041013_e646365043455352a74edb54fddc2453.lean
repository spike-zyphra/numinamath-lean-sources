import Mathlib
/- If $\frac{3x^2-4x+1}{x-1}=m$, and $x$ can be any real number except $1$, what real values can $m$ NOT have?-/
theorem algebra_20995 (m : ℝ) :
    (∃ x, x ≠ 1 ∧ (3 * x ^ 2 - 4 * x + 1) / (x - 1) = m) →  m ≠ 2 := by 
      intro h
      rcases h with ⟨x,⟨h1,h2⟩⟩
      --We notice that the numerator of the fraction factors into $(3x-1)(x-1)$. Substituting this into the given expression, we get $m=\dfrac{3x^2-4x+1}{x-1} = \dfrac{(3x-1)(x-1)}{x-1}$. This simplifies to $m=3x-1$ if $x$ is not 1. Thus, $m$ can be any real number except for the value it takes when $x$ is $1.$ This value is $3(1)-1=3-1=\boxed{2}$.
      rw [show (3 * x ^ 2 - 4 * x + 1) = (3 * x - 1)*(x - 1) by ring_nf] at h2
      have hneq : x - 1 ≠ 0 := by
        contrapose! h1
        have e :=  congrArg ( fun (t) => (t) + 1 ) h1; simp at e
        exact e
      have h3 : (x-1) / (x-1) = 1 := by
        apply div_self hneq
      rw[show (3 * x - 1) * (x - 1) / (x - 1) = (3 * x - 1) * ((x - 1) / (x - 1)) by ring_nf] at h2
      rw[h3] at h2
      contrapose! h1
      rw[h1] at h2
      ring_nf at h2
      have e :=  congrArg ( fun (t) => ((t) + 1) / 3) h2; simp at e; ring_nf at e
      exact e
   
      