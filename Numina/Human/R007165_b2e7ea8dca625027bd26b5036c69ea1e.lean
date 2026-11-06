import Mathlib

/- Show that there are infinitely many positive integers solutions to $2 a^{2}-3 a+1=3 b^{2}+b$. -/
theorem number_theory_604329 :
    {(a, b) : ℤ × ℤ | a > 0 ∧ b > 0 ∧ 2 * a ^ 2 - 3 * a + 1 = 3 * b ^ 2 + b}.Infinite := by

  -- We introduce notation for the key predicate.
  let P : ℤ × ℤ → Prop
  | (a, b) => 0 < a ∧ 0 < b ∧ 2 * a ^ 2 - 3 * a + 1 = 3 * b ^ 2 + b

  -- And an auxillary predicate.
  let Q : ℤ × ℤ → Prop
  | (n, d) => 0 < n ∧ 0 < d ∧ n ^ 2 - 6 * d ^ 2 = 1

  -- We also introduce two functions, firstly `f`:
  let f_aux : ℤ × ℤ → ℤ × ℤ := fun (n, d) ↦ (2 * n ^ 2 - 1, 2 * n * d)
  let f (n : ℕ) := Nat.iterate f_aux n (5, 2)

  -- And also a function `g`:
  -- Given $n,d$, let $a = d(n+3 d)/(n^{2}-6 d^{2}) + 1$ and $b = d(n+2d)/(n^{2}-6 d^{2})$.
  let g_a (n d : ℤ) := d * (n + 3 * d) / (n ^ 2 - 6 * d ^ 2) + 1
  let g_b (n d : ℤ) := d * (n + 2 * d) / (n ^ 2 - 6 * d ^ 2)
  let g : ℤ × ℤ → ℤ × ℤ := fun (n, d) ↦ (g_a n d, g_b n d)

  -- It suffices to prove that `{x | P x}` is an infinite set.
  -- We will show that
  -- - `f` maps from `ℕ` to `{x | Q x}` injectively,
  -- - `g` maps from `{x | Q x}` to `{x | P x}` injectively.
  -- Consequently the required conclusion follows from the infinitude of `ℕ`.

  -- The range of $f$ is contained is set `{x | Q x}`
  have hfQ (n : ℕ) : Q (f n) := by
    -- We verify that $n=5$, $d=2$ satisfies this equation so there is at least one solution.
    have hfzero : Q (5, 2) := by
      all_goals decide
    -- Given solution $n,d$ there there exists solution $n',d'$ such that $n < n'$, $d < d'$
    have hfsucc (x : ℤ × ℤ) (h : Q x) : Q (f_aux x) := by
      dsimp [Q]
      obtain ⟨hn , hd, hQ⟩ := h
      constructor
      · nlinarith
      · constructor
        · nlinarith
        · calc
            _ = (2 * x.1 ^ 2 - 1) ^ 2 - 24 * x.1 ^ 2 * x.2 ^ 2 := by ring_nf
            _ = (4 * x.1 ^ 4 - 4 * x.1 ^ 2 + 1) - 24 * x.1 ^ 2 * x.2 ^ 2 := by linarith
            _ = 4 * x.1 ^ 2 * (x.1 ^ 2 - 6 * x.2 ^ 2 - 1) + 1 := by linarith
            _ = 1 := by
              rw [hQ]
              simp
    induction' n with n hi
    · exact hfzero
    · rw [show f (n + 1) = f_aux (f n) by exact (Function.iterate_succ_apply' f_aux n (5, 2))]
      exact hfsucc (f n) hi

  -- `g` is injective on `{x | Q x}`
  have hInj_g : Set.InjOn g {x | Q x} := by
    -- We argue by contradiction
    by_contra hc
    dsimp [Set.InjOn] at hc
    push_neg at hc
    obtain ⟨x, hx, y , hy, hxy, hxy'⟩ := hc
    rw [Prod.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    dsimp [g_a] at h1
    rw [hx.2.2, hy.2.2, EuclideanDomain.div_one, EuclideanDomain.div_one] at h1
    dsimp [g_b] at h2
    rw [hx.2.2, hy.2.2, EuclideanDomain.div_one, EuclideanDomain.div_one] at h2
    -- The equations `h1`, `h2`, together with the positivity of `x.2`, `y.2`, implies that `x = y`.
    have : x.2 ^ 2 = y.2 ^ 2 := calc
      _ = x.2 * (x.1 + 3 * x.2) - x.2 * (x.1 + 2 * x.2) := by linarith
      _ = y.2 * (y.1 + 3 * y.2) - y.2 * (y.1 + 2 * y.2) := by linarith
      _ = y.2 ^ 2 := by
        linarith
    obtain h2eq | h := eq_or_eq_neg_of_sq_eq_sq x.2 y.2 this
    · rw [← h2eq] at h1
      simp (disch := field_simp_discharge) only [mul_eq_mul_left_iff, add_left_inj] at h1
      obtain h1eq | _ := h1
      · exact hxy' (show x = y by rw [Prod.mk.injEq]; exact ⟨h1eq, h2eq⟩)
      · linarith [hx.2.1]
    · have : x.2 < x.2 := calc
        _ = -y.2 := h
        _ < 0 := by linarith [hy.2.1]
        _ < _ := hx.2.1
      exact (lt_self_iff_false x.2).mp this

  -- `f` is injective on `ℕ`
  have hInj_f : Function.Injective f := by
    -- The function is strictly monotone in both coordinates
    have mono {n k : ℕ} : (1 < (f n).1 ∧ 1 < (f n).2) ∧
        (k < n → (f k).1 < (f n).1 ∧ (f k).2 < (f n).2) := by
      induction' n with n hi
      · constructor
        · decide
        · omega
      · have mono1 : (f n).1 < (f (n + 1)).1 := by
          have : (f (n + 1)).1 = 2 * (f n).1 ^ 2 - 1 := by
            rw [show f (n + 1) = f_aux (f n) by exact Function.iterate_succ_apply' f_aux n (5, 2)]
          rw [this]
          nlinarith [hi.1]
        have mono2 : (f n).2 < (f (n + 1)).2 := by
          have : (f (n + 1)).2 = 2 * (f n).1 * (f n).2 := by
            rw [show f (n + 1) = f_aux (f n) by exact Function.iterate_succ_apply' f_aux n (5, 2)]
          rw [this]
          nlinarith
        constructor
        · have h := calc
            1 < (f n).1 := hi.1.1
            _ < (f (n + 1)).1 := mono1
          have h' := calc
            1 < (f n).2 := hi.1.2
            _ < (f (n + 1)).2 := mono2
          exact ⟨h, h'⟩
        · intro hk
          rcases (by omega : k = n ∨ k < n) with hk | hk
          · constructor
            · rwa [hk]
            · rwa [hk]
          · constructor
            · calc
              _ < (f n).1 := (hi.2 hk).1
              _ < _ := mono1
            · calc
              _ < (f n).2 := (hi.2 hk).2
              _ < _ := mono2
    by_contra hc
    dsimp [Function.Injective] at hc
    push_neg at hc
    obtain ⟨n, k, hfnk, hnk⟩ := hc
    rcases (by omega : k < n ∨ n < k) with hc | hc
    all_goals
    · have h := mono.2 hc
      rw [(Prod.ext_iff.mp hfnk).1] at h
      exact (lt_self_iff_false (f k).1).mp h.1

  -- If $n, d$ satisfy ${n}^{2}-6 {d}^{2}=1$ then $a,b$ as defined above satisfy the key equality.
  have hMapsTo_gQP : Set.MapsTo g {x | Q x} {x | P x} := by
    intro x ⟨hn, hd, hQ⟩
    have g1 : 0 < g_a x.1 x.2 := by
      dsimp [g_a]
      rw [hQ, EuclideanDomain.div_one]
      nlinarith
    have g2 : 0 < g_b x.1 x.2 := by
      dsimp [g_b]
      rw [hQ, EuclideanDomain.div_one]
      nlinarith
    have g3 : 2 * g_a x.1 x.2 ^ 2 - 3 * g_a x.1 x.2 + 1 = 3 * g_b x.1 x.2 ^ 2 + g_b x.1 x.2 := by
      dsimp [g_a, g_b]
      simp [hQ, EuclideanDomain.div_one]
      nlinarith
    exact ⟨g1, g2, g3⟩

  -- The set `{x | Q x}` is infinite
  have hInfiniteQ : {x | Q x}.Infinite := by
    -- We know that `f` is injective and that the range of `f` is contained within `{x | Q x}`.
    have h : (Set.range f).Infinite := by
      refine Set.infinite_range_of_injective hInj_f
    have h' : (Set.range f) ⊆ {x | Q x} := by
      rintro x ⟨n, hn⟩
      rw [← hn]
      exact hfQ n
    exact Set.Infinite.mono h' h

  -- The set `{x | P x}` is infinite since `{x | Q x}` is infinite, the image under `g` of
  -- `{x | Q x}` is contained within `{x | P x}` and `g` is injective.
  have hInfiniteP : {x | P x}.Infinite := Set.infinite_of_injOn_mapsTo hInj_g hMapsTo_gQP hInfiniteQ

  exact hInfiniteP
