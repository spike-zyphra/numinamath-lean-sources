import Mathlib
/- Determine all pairs $(f, g)$ of functions from the set of real numbers to itself that satisfy  $$ g(f(x+y))=f(x)+(2 x+y) g(y) $$  for all real numbers $x$ and $y$.  Answer. Either both $f$ and $g$ vanish identically, or there exists a real number $C$ such that $f(x)=x^{2}+C$ and $g(x)=x$ for all real numbers $x$. -/
theorem number_theory_24103 : {(f, g) : (ℝ → ℝ) × (ℝ → ℝ) | ∀ x y : ℝ, g (f (x + y)) = f (x) + (2 * x + y) * g y} = {(f, g) : (ℝ → ℝ) × (ℝ → ℝ) | f = 0 ∧ g = 0} ∪ {(f, g) : (ℝ → ℝ) × (ℝ → ℝ) | ∃ c : ℝ, (f = fun (x : ℝ) => x ^ 2 + c) ∧ (g = fun (y : ℝ) => y)}:= by
  -- We use extensionality to prove equality of sets of function pairs
  ext ⟨f, g⟩
  constructor
  -- Forward direction: if (f,g) satisfies the functional equation, then it's in our solution set
  .
    intro h
    simp at h
    -- Derive a key relationship between f and g by swapping x and y in the functional equation
    have h1 : ∀ x y : ℝ, f x - f y = (2 * y + x) * g x - (2 * x + y) * g y:= by
      intro x y
      have g1:= h x y
      have g2:= h y x
      rw [show y + x = x + y by ring] at g2
      linarith
    -- Show that g must be a linear function
    have h2 : g = fun x => x * (g 1 - g 0) + g 0:= by
      funext x
      have g1:= h1 x 0
      have g2:= h1 1 x
      have g3:= h1 0 1
      linarith
    -- Define constants to simplify our work
    set A:= g 1 - g 0
    set B:= g 0
    set C:= f 0 with hC
    clear_value A B C
    subst g
    simp at h
    -- Case analysis based on whether A = 0 or not
    by_cases hA : A = 0
    -- Case 1: A = 0, which means g is constant
    .
      subst A
      simp at h
      -- Show that B must be 0, making g the zero function
      have hB : B = 0:= by
        have g1:= h 0 0
        have g2:= h 0 1
        linarith
      subst B
      simp at h
      -- Show that f must also be the zero function
      replace h : f = fun x => 0:= by
        funext x
        specialize h x
        linarith
      subst f
      simp
      left
      funext _
      simp
    -- Case 2: A ≠ 0, which leads to the quadratic solution
    .
      -- Show that f must be a quadratic function
      have h2 : ∀ x : ℝ, f x = x ^ 2 + B / A * x + (C - B) / A:= by
        intro x
        have h2:= h 0 x
        simp at h2
        subst C
        field_simp
        linarith
      simp [h2] at h
      field_simp at h
      -- Derive additional constraints by evaluating at specific points
      have g1:= h 0 0
      have g2:= h (-1) 0
      have g3:= h 1 0
      simp at g1 g2 g3
      ring_nf at g1 g2 g3
      -- Show that either B = 0 or A = -1
      have g4 : B * (A + 1) = 0:= by linarith
      simp at g4
      rcases g4 with g4 | g4
      -- Subcase: B = 0
      .
        subst B
        simp at g1 g2
        -- Show that A = 1
        replace g2 : A * (A - 1) = 0:= by linarith
        simp [hA] at g2
        replace g2 : A = 1:= by linarith
        subst A
        simp at h2
        simp
        right
        -- Conclude that f(x) = x² + C and g(x) = x
        use C
        funext x
        specialize h2 x
        exact h2
      -- Subcase: A = -1
      .
        replace g4 : A = -1:= by linarith
        subst A
        simp at g1 g2
        replace g1 : B = 2 * C:= by linarith
        subst B
        linarith
  -- Reverse direction: if (f,g) is in our solution set, then it satisfies the functional equation
  .
    intro h
    simp at h
    rcases h with h | h
    -- Case 1: f = 0 and g = 0
    .
      rcases h with ⟨hf, hg⟩
      subst f g
      simp
    -- Case 2: f(x) = x² + c and g(x) = x
    .
      rcases h with ⟨⟨c, hf⟩, hg⟩
      subst f g
      simp
      intro x y
      linarith
