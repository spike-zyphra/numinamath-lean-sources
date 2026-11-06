import Mathlib
/- Find all functions $f: \mathbb{Q} \rightarrow \mathbb{Q}$ such that  $$ f(x)+f(t)=f(y)+f(z) $$  for all rational numbers $x< y< z< t$ that form an arithmetic progression. -/
theorem algebra_604788 : {f : ℚ → ℚ | ∀ x y z t, x < y ∧ y < z ∧ z < t ∧ (∃ d, y = x + d ∧ z = y + d ∧ t = z + d) → f x + f t = f y + f z} = {f : ℚ → ℚ | ∃ a b : ℚ, f = fun x => a + b * x}:= by
  ext f
  constructor
  .
    -- Forward direction: If f satisfies the functional equation, then f is an affine function
    intro h
    simp at h

    -- Simplify the condition to a more manageable form with explicit d > 0
    replace h : ∀ x d : ℚ, d > 0 → f x + f (x + 3 * d) = f (x + d) + f (x + 2 * d):= by
      intro x d hd
      specialize h x (x + d) (x + 2 * d) (x + 3 * d) (by linarith) (by linarith)  (by linarith) d (by linarith) (by linarith) (by linarith)
      exact h

    -- Extend the condition to all d (positive, zero, or negative)
    replace h : ∀ x d : ℚ, f x + f (x + 3 * d) = f (x + d) + f (x + 2 * d):= by
      intro x d
      by_cases hd : d > 0
      .
        specialize h x d hd
        exact h
      .
        by_cases hd1 : d = 0
        .
          subst d
          simp
        .
          simp at hd
          replace hd : d < 0:= by
              by_contra H
              simp at H
              replace H : d = 0:= by linarith
              trivial
          specialize h (x + 3 * d) (-d) (by linarith)
          ring_nf at h ⊢
          exact h

    -- Derive the key functional equation: f(x-d) + f(x+d) = 2*f(x)
    -- This is the Jensen's functional equation for midpoint convexity
    replace h : ∀ x d : ℚ, f (x - d) + f (x + d) = 2 * f x:= by
      intro x d
      have h1:= h (x - d / 2) (d / 2)
      have h2:= h (x - d) (d / 2)
      ring_nf at h1 h2 ⊢
      linarith

    -- Show that consecutive differences are equal when points are equally spaced
    have h1 : ∀ d : ℚ, d ≠ 0 → ∀ n : ℕ, f ((n + 1) / d) - f (n / d) = f ((n + 2) / d) - f ((n + 1) / d):= by
      intro d _ n
      specialize h ((n + 1) / d) (1 / d)
      ring_nf at h ⊢
      linarith

    -- Prove that the differences are constant (first difference is constant)
    replace h1 : ∀ d : ℚ, d ≠ 0 → ∃ c : ℚ, (∀ n : ℕ, f ((n + 1) / d) - f (n / d) = c):= by
      intro d hd
      use f (1 / d) - f 0
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [←ih]
        specialize h1 d hd n
        simp
        rw [show (↑n : ℚ) + 1 + 1 = n + 2 by linarith]
        rw [h1]

    -- Establish that f(n/d) follows an arithmetic progression formula
    replace h1 : ∀ d : ℚ, d ≠ 0 → (∀ n : ℕ, f (n / d) = f 0 + (f (1 / d) - f 0) * n):= by
      intro d hd
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        have g1:= h1 d hd
        rcases g1 with ⟨c, hc⟩
        have g1:= hc 0
        simp at g1
        field_simp at g1
        rw [←g1] at hc
        specialize hc n
        rw [ih] at hc
        simp at hc
        simp
        linarith

    -- Relate f(1) to f(0) and the slope
    have h2 : ∀ d : ℕ, d ≠ 0 → f 1 = f 0 + (f (1 / d) - f 0) * d:= by
      intro d hd
      specialize h1 d (by qify at hd ; exact hd) d
      simp at h1
      field_simp at h1
      exact h1

    -- Construct the affine function f(x) = a + b*x where a = f(0) and b = f(1) - f(0)
    simp
    use f 0, f 1 - f 0
    ext x

    -- Express any rational x as a fraction p/q in lowest terms
    have g1 : x = x.num / x.den:= by exact Eq.symm (Rat.num_div_den x)
    have hq : x.den > 0:= by exact Rat.den_pos x
    set p:= x.num
    set q:= x.den
    clear_value p q

    -- Case analysis based on the numerator p
    by_cases hp : p = 0
    .
      -- Case: x = 0
      subst p
      simp at g1
      subst x
      simp
    .
      -- Case: p ≠ 0 (either positive or negative)
      replace hp : p < 0 ∨ p > 0:= by omega

      -- Establish the formula for positive integer numerators
      have h3 : ∀ d : ℕ, d ≠ 0 → ∀ p : ℤ, p > 0 → f (p / d) = f 0 + (f 1 - f 0) * (p / d):= by
        intro d hd p hp
        specialize h1 d (by qify at hd ; exact hd) p.natAbs
        rw [show (↑p.natAbs : ℚ) = (↑(↑p.natAbs : ℤ) : ℚ) by rfl] at h1
        simp at h1
        qify at hp
        rw [abs_of_pos hp] at h1
        field_simp at h1
        specialize h2 d hd
        replace h2 : (f 1 - f 0) / d + f 0 = f (1 / d):= by
          field_simp
          linarith
        rw [←h2] at h1
        rw [h1]
        simp
        field_simp

      -- Handle both negative and positive numerator cases
      rcases hp with hp | hp
      .
        -- Case: p < 0 (negative numerator)
        specialize h 0 (p / q)
        simp at h
        specialize h3 q (by omega) (-p) (by omega)
        simp at h3
        rw [show -(p / (q : ℚ)) = -p / q by field_simp] at h
        rw [h3] at h
        subst x
        replace h : f (↑p / ↑q) = f 0 - (f 1 - f 0) * (-↑p / ↑q):= by linarith
        rw [h]
        field_simp
      .
        -- Case: p > 0 (positive numerator)
        specialize h3 q (by omega) p (by omega)
        subst x
        exact h3
  .
    -- Reverse direction: If f is an affine function, then it satisfies the functional equation
    intro h
    simp at h
    rcases h with ⟨a, b, hf⟩
    simp
    intro x y z t h1 h2 h3 d hy hz ht
    subst y z t
    ring_nf
    clear h1 h2 h3
    simp [hf]
    ring_nf
