import Mathlib
/- Find all functions $f: \mathbb{Z} \rightarrow \mathbb{Z}$ for which $f(g(n))-g(f(n))$ is independent on $n$ for any $g: \mathbb{Z} \rightarrow \mathbb{Z}$. -/
theorem algebra_605146 (f : ℤ → ℤ) : (∀ g : ℤ → ℤ, ∃ c : ℤ, ∀ n : ℤ, f (g n) - g (f n) = c) ↔ ((∃ d : ℤ, ∀ n : ℤ, f n = d) ∨ (∀ n : ℤ, f n = n)):= by
  constructor
  -- Forward direction (⟹)
  .
    intro h
    -- Case analysis: either f(n) = n for all n, or not
    by_cases h1 : ∀ n : ℤ, f n = n
    .
      right
      exact h1
    .
      simp at h1
      rcases h1 with ⟨x, hx⟩
      -- Define helper function g1 that maps f(x) to 1 and everything else to 0
      set g1 : ℤ → ℤ := fun n => if n = f x then 1 else 0 with hg1
      clear_value g1
      -- Prove that if n ≠ f(x), then f(n) = f(x)
      have h1 : ∀ n : ℤ, n ≠ f x → f n = f x:= by
        intro n hn
        have h1:= h g1
        rcases h1 with ⟨c, hc⟩
        have h1:= hc n
        have h2:= hc x
        have h3 : f (g1 n) = f 0:= by simp [hg1, hn]
        have h4 : f (g1 x) = f 0:= by
          replace hx : x ≠ f x:= by exact fun a => hx (id (Eq.symm a))
          simp [hg1, hx]
        have h5 : g1 (f n) = g1 (f x):= by linarith
        simp [hg1] at h5
        exact h5
      -- Define two distinct values a and b around f(x)
      set a:= f x + 1 with ha
      set b:= f x - 1 with hb
      have hab : a ≠ b:= by
        by_contra H
        linarith
      -- Prove f(a) = f(x) and f(b) = f(x)
      have ha1 : f a = f x:= by
        have ha1 : a ≠ f x:= by linarith
        exact h1 a ha1
      have hb1 : f b = f x:= by
        have hb1 : b ≠ f x:= by linarith
        exact h1 b hb1
      clear_value a b
      clear hg1 g1
      -- Define new helper function g1 that maps f(x) to a and everything else to b
      set g1 : ℤ → ℤ:= fun n => if n = f x then a else b with hg1
      clear_value g1
      -- Prove that f(f(x)) = f(x)
      have h2 : f (f x) = f x:= by
        have h2:= h g1
        rcases h2 with ⟨c, hc⟩
        have h2:= hc (f x)
        have h3:= hc x
        have h4 : f (g1 (f x)) = f a:= by simp [hg1]
        have h5 : f (g1 x) = f b:= by
          replace hx : x ≠ f x:= by exact fun a => hx (id (Eq.symm a))
          simp [hg1, hx]
        have h6 : g1 (f (f x)) = g1 (f x):= by linarith
        simp [hg1] at h6
        by_contra H
        replace h6:= h6 H
        replace h6 : a = b:= by linarith
        trivial
      -- Conclude that f is constant with value f(x)
      left
      use (f x)
      intro n
      by_cases hn : n = f x
      .
        subst n
        exact h2
      .
        specialize h1 n hn
        exact h1
  -- Backward direction (⟸)
  .
    intro h
    rcases h with h | h
    .
      rcases h with ⟨d, hd⟩
      simp [hd]
    .
      simp [h]
