import Mathlib
/- We are given $a$ and $b$, find all functions $f: \mathbb{Q} \rightarrow \mathbb{Q}$ such that:

$$
f(x+a+f(y))=f(x+b)+y
$$ -/
theorem algebra_132091 (a b : ℚ) : {f : ℚ → ℚ | ∀ x y : ℚ, f (x + a + f y) = f (x + b) + y} = {fun (x : ℚ) => x + b - a, fun (x : ℚ) => -x + b - a}:= by
  -- We use extensionality to prove equality of sets
  ext f
  constructor
  .
    intro h
    simp at h
    -- Prove that f is injective
    have h1 : ∀ x y : ℚ, f x = f y → x = y:= by
      intro x y h1
      have g1:= h 0 x
      have g2:= h 0 y
      rw [h1] at g1
      linarith
    -- Simplify the functional equation for specific values
    have h2 : ∀ y : ℚ, f (-b + a + f y) = f 0 + y:= by
      intro y
      specialize h (-b) y
      simp at h
      exact h
    -- Another specialized form of the functional equation
    have h3 : ∀ x : ℚ, f (x + -b + a + f (f 0)) = f x + f 0:= by
      intro x
      specialize h (x + -b) (f 0)
      simp at h
      exact h
    -- Derive a formula for f(f(x))
    have h4 : ∀ x : ℚ, f (f x) = x + f (f 0):= by
      intro x
      specialize h2 (f x)
      specialize h3 x
      specialize h1 (-b + a + f (f x)) (x + -b + a + f (f 0)) (by linarith)
      linarith
    -- Derive a formula for f(x+y)
    have h5 : ∀ x y : ℚ, f (x + y) = f x + f y + a - b:= by
      intro x y
      specialize h (f x - b) y
      simp at h
      rw [h4 x] at h
      rw [show x + f (f 0) + y = x + y + f (f 0) by ring] at h
      rw [←h4 (x + y)] at h
      specialize h1 (f x - b + a + f y) (f (x + y)) h
      linarith
    -- Define a new function g to simplify the analysis
    set g:= fun (x : ℚ) => f x + (a - b) with hg
    clear_value g
    -- Show that g is additive: g(x+y) = g(x) + g(y)
    replace h5 : ∀ x y : ℚ, g (x + y) = g x + g y:= by
      intro x y
      simp [hg]
      specialize h5 x y
      linarith
    clear h1 h2 h3 h4
    -- Prove that any additive function g must be of the form g(x) = g(1) * x
    have h6 : ∀ g : ℚ → ℚ, (∀ x y : ℚ, g (x + y) = g x + g y) → ∀ x : ℚ, g x = g 1 * x:= by
      intro g h5 x
      -- Express x as a rational number
      rw [show x = x.num / x.den by exact Eq.symm (Rat.num_div_den x)]
      set b:= x.den with hb
      clear_value b
      -- Prove that g(-x) = -g(x)
      have h1 : ∀ x : ℚ, g (-x) = -g x:= by
        intro x
        have g1:= h5 0 0
        simp at g1
        specialize h5 x (-x)
        simp at h5
        linarith
      -- Prove a formula for g(k/n)
      have h2 : ∀ n : ℕ, n > 0 → ∀ k : ℕ, g ((↑k : ℚ) / n) = k * g ((1 : ℚ) / n):= by
        intro n hn k
        induction k with
        | zero =>
          simp
          specialize h5 0 0
          simp at h5
          exact h5
        | succ k ih =>
          simp
          specialize h5 ((↑k : ℚ) / n) ((1 : ℚ) / n)
          rw [show (↑k : ℚ) / n +  (1 : ℚ) / n = (k + 1) / n by field_simp] at h5
          rw [h5, ih]
          simp
          linarith
      -- Prove that g(c/b) = g(1) * (c/b) for non-negative integers c
      have h3 : ∀ c : ℤ, c ≥ 0 → g (↑c / ↑b) = g 1 * (↑c / ↑b):= by
        intro c hpos
        set a:= c.natAbs with ha
        clear_value a
        qify at ha hpos
        rw [abs_of_nonneg hpos] at ha
        rw [←ha]
        clear ha
        induction a with
        | zero =>
          simp
          specialize h5 0 0
          simp at h5
          exact h5
        | succ a ih =>
          simp
          have hbpos : b > 0:= by
            subst b
            exact Rat.den_pos x
          specialize h2 b hbpos b
          field_simp at h2
          specialize h5 ((↑a : ℚ) / b) ((1 : ℚ) / b)
          rw [show (↑a : ℚ) / b +  (1 : ℚ) / b = (a + 1) / b by field_simp] at h5
          rw [h5, ih]
          replace h2 : g ((1 : ℚ) / b) = g 1 / b:= by
            field_simp
            rw [h2]
            ring_nf
          rw [h2]
          ring_nf
      -- Handle both positive and negative numerators
      by_cases hpos : x.num ≥ 0
      .
        exact h3 (x.num) hpos
      .
        replace hpos : x.num < 0:= by exact Int.lt_of_not_ge hpos
        specialize h3 (-x.num) (by linarith)
        simp at h3
        set t:= (↑x.num : ℚ) / b with ht
        clear_value t
        rw [show -(↑x.num : ℚ) / b = -t by subst t ; ring_nf] at h3
        rw [h1 t] at h3
        linarith only [h3]
    -- Apply the result to our function g
    specialize h6 g h5
    subst g
    simp at h6
    clear h5
    -- Express f in terms of f(1)
    replace h6 : f = fun x => (f 1 + (a - b)) * x + b - a:= by funext x ; linarith only [h6 x]
    rw [h6] at h
    simp at h
    set s:= f 1 + (a - b) with hs
    clear_value s
    -- Determine the possible values of s
    specialize h 1 1
    ring_nf at h
    replace h : (s + 1) * (s - 1) = 0:= by linarith
    simp at h
    -- s must be either -1 or 1
    rcases h with h | h
    .
      -- Case s = -1
      replace h : s = -1:= by linarith
      clear hs
      subst s f
      simp
    .
      -- Case s = 1
      replace h : s = 1:= by linarith
      clear hs
      subst s f
      simp
  .
    -- Prove the reverse direction: both candidate functions satisfy the functional equation
    intro h
    simp at h
    rcases h with h | h
    all_goals
      subst f
      simp
      intro x y
      linarith
