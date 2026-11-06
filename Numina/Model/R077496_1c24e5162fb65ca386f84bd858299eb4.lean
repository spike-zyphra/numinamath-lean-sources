import Mathlib

theorem algebra_10246 {f g h : ℝ → ℝ}
    (hf : f = fun x => (x - 1) * (x - 3) / 2)
    (hg : g = fun x => -f x)
    (hh : h = fun x => f (-x)) :
    Set.ncard {x | f x = g x} * 10 + Set.ncard {x | f x = h x} = 21 := by
  have h1 : {x | f x = g x} = {1, 3} := by
    ext x
    simp [hf, hg]
    constructor
    · -- Assume $f(x) = g(x)$, we need to prove $x \in \{1, 3\}$
      intro h
      have h2 : (x - 1) * (x - 3) = 0 := by
        ring_nf at h ⊢
        linarith
      cases' (mul_eq_zero.mp h2) with h3 h4
      · -- Case $x - 1 = 0$, so $x = 1$
        left
        linarith
      · -- Case $x - 3 = 0$, so $x = 3$
        right
        linarith
    · -- Assume $x \in \{ 1, 3 \}$, prove $f(x) = g(x)$
      rintro (h | h)
      · -- $x = 1$
        rw [h]
        norm_num [hf]
      · -- $x = 3$
        rw [h]
        norm_num [hf]
  
  have h4 : {x | f x = h x} = {0} := by
    ext x
    simp [hf, hh]
    constructor
    · -- Assume $f(x) = h(x)$ prove $x = 0$
      intro h
      have h5 : x * (x) = 0 := by
        ring_nf at h ⊢
        nlinarith
      cases' (mul_eq_zero.mp h5) with h6 h7
      · -- Case $x = 0$
        linarith
      · -- Case $x = 0$
        linarith
    · -- Assume x = 0 prove f(x) = h(x)
      intro h
      rw [h]
      norm_num [hf]
  rw [h1, h4]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]