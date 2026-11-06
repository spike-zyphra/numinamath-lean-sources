import Mathlib

/- Given a function $f$ for which $f(x) = f(398 - x) = f(2158 - x) = f(3214 - x)$ holds for all real $x$,
what is the largest number of different values that can appear in the list $f(0), f(1), f(2), \ldots, f(999)$? -/
theorem algebra_97235 : IsGreatest {n | ∃ f : ℝ → ℝ,
    (∀ x, f x = f (398 - x) ∧ f (398 - x) = f (2158 - x) ∧ f (2158 - x) = f (3214 - x)) ∧
    n = {y | ∃ x : ℤ, 0 ≤ x ∧ x ≤ 999 ∧ f x = y}.ncard} 177 := by

  -- First, note that the conditions on $f$ can be simplified to just two:
  have f_conditions_iff {f : ℝ → ℝ} :
      (∀ x, f x = f (398 - x) ∧ f (398 - x) = f (2158 - x) ∧ f (2158 - x) = f (3214 - x)) ↔
      (∀ x, f (x + 352) = f x) ∧ (∀ x, f (398 - x) = f x) := by
    constructor
    . intro hf
      -- From the given conditions, we know $f$ is periodic with both period 1056 and period 1760.
      have f_1056 x : f (x + 1056) = f x := by
        symm
        calc
          f x = f (2158 - (2158 - x)) := by ring_nf
          _ = f (3214 - (2158 - x)) := (hf (2158 - x)).2.2
          _ = f (x + 1056) := by ring_nf
      have f_1760 x : f (x + 1760) = f x := by
        symm
        calc
          f x = f (398 - (398 - x)) := by ring_nf
          _ = f (2158 - (398 - x)) := (hf (398 - x)).2.1
          _ = f (x + 1760) := by ring_nf
      -- Thus $f$ is periodic by their GCD 352 too, using Bézout's identity.
      have f_352 x : f (x + 352) = f x := by
        let k1 : ℤ := Int.gcdA 1056 1760
        let k2 : ℤ := Int.gcdB 1056 1760
        have : (352 : ℝ) = k1 * 1056 + k2 * 1760 := by
          norm_cast
          move_mul [k1, k2]
          simp [k1, k2]
          rw [← Int.gcd_eq_gcd_ab 1056 1760]
          norm_num
        rw [this, ← add_assoc, Function.Periodic.int_mul f_1760 k2, Function.Periodic.int_mul f_1056 k1]
      exact ⟨f_352, fun x => symm (hf x).1⟩
    . rintro ⟨f_352, f_398⟩ x
      and_intros
      . exact symm (f_398 x)
      . let k : ℤ := 5
        have : (2158 - x) = (398 - x) + k * 352 := by simp [k]; ring
        rw [this, Function.Periodic.int_mul f_352 k]
      . let k : ℤ := 3
        have : (3214 - x) = (2158 - x) + k * 352 := by simp [k]; ring
        rw [this, Function.Periodic.int_mul f_352 k]

  -- These conditions imply that for any integer $n$, $f(n) = f(m)$ for some $m ∈ [23, 199]$, so that
  -- the set of $f(0), f(1), f(2), \ldots, f(999)$ is the same as the image of $f$ restricted to $[23, 199]$.
  have f_range {f : ℝ → ℝ} (hf : ∀ x, f x = f (398 - x) ∧ f (398 - x) = f (2158 - x) ∧ f (2158 - x) = f (3214 - x)) :
      {y | ∃ x : ℤ, 0 ≤ x ∧ x ≤ 999 ∧ f x = y} = (fun (x : ℤ) => f ↑x) '' (Finset.Icc (23 : ℤ) (199 : ℤ)) := by
    ext x
    simp [Set.mem_image]
    obtain ⟨f_352, f_398⟩ := f_conditions_iff.mp hf
    constructor
    . rintro ⟨n, ⟨_, _, hn⟩⟩
      -- First, we can map $n$ into the range $[23, 375)$ using the periodicity of $f$.
      let n' := (n - 23) % 352 + 23
      have hn' : f n' = x := by
        let k := (n - 23) / 352
        have : n' = n - k * 352 := by omega
        rw [this, ← hn]
        push_cast
        exact Function.Periodic.sub_int_mul_eq f_352 k
      -- Then, if $n' > 199$, we can map it into the range $[23, 199]$ using the second property.
      by_cases h : n' > 199
      . let n'' := 398 - n'
        have hn'' : f n'' = x := by
          simp [n'']
          rw [← hn', f_398]
        exact ⟨n'', ⟨by omega, by omega⟩, hn''⟩
      . -- If $n' ≤ 199$ already, we are done.
        exact ⟨n', ⟨by omega, by omega⟩, hn'⟩
    . -- The other direction is trivial since $[23, 199]$ is a subset of $[0, 999]$.
      rintro ⟨m, ⟨_, hm⟩⟩
      exact ⟨m, by omega, by omega, hm⟩

  and_intros
  swap
  . -- Since $[23, 199]$ has cardinality 177, the set $f(23), f(24), \ldots, f(199)$ can have at most 177 distinct values.
    intro n nh
    rcases nh with ⟨f, hf, hn⟩
    rw [hn]
    calc
      {y | ∃ x : ℤ, 0 ≤ x ∧ x ≤ 999 ∧ f x = y}.ncard = Nat.card {y | ∃ x : ℤ, 0 ≤ x ∧ x ≤ 999 ∧ f x = y} := by rw [Set.Nat.card_coe_set_eq]
      _ = Nat.card ((fun (x : ℤ) => f ↑x) '' (Finset.Icc (23 : ℤ) (199 : ℤ))) := by rw [f_range hf]
      _ ≤ Nat.card (Finset.Icc (23 : ℤ) (199 : ℤ)) := Nat.card_image_le (Finite.of_fintype (Finset.Icc (23 : ℤ) (199 : ℤ)))
      _ = Finset.card (Finset.Icc (23 : ℤ) (199 : ℤ)) := by rw [Nat.card_eq_finsetCard]
      _ = 177 := by simp
  . -- Next we must show that this bound is actually achieved for some function.
    -- We choose a shifted and scaled cosine function and show that it satisfies the conditions.
    let g : ℝ → ℝ := fun x => (2 * Real.pi / 352) * (x - 23)
    have g_352 x : g (x + 352) = g x + 2 * Real.pi := by simp [g]; ring_nf
    have g_398 x : g (398 - x) = 2 * Real.pi - g x := by simp [g]; ring_nf
    have g_inj x y : g x = g y → x = y := by simp [g, Real.pi_ne_zero]
    have g_monotone x y : x ≤ y → g x ≤ g y := by
      rintro hxy
      refine mul_le_mul_of_nonneg_left ?_ ?_
      . simp [hxy]
      . positivity
    have g_23 : g 23 = 0 := by simp [g]
    have g_199 : g 199 = Real.pi := by ring_nf
    let f : ℝ → ℝ := fun x => Real.cos (g x)
    have f_352 : ∀ x, f (x + 352) = f x := by simp [f, g_352]
    have f_398 : ∀ x, f (398 - x) = f x := by simp [f, g_398]
    use f
    obtain hf := f_conditions_iff.mpr ⟨f_352, f_398⟩
    use hf
    -- This achieves all values on integers in the range $[23, 199]$ since $f$ is strictly increasing on this interval.
    have f_inj : Set.InjOn (fun (x : ℤ) => f ↑x) (Finset.Icc (23 : ℤ) (199 : ℤ)) := by
      simp [f]
      rintro x hx y hy hf
      simp at hf
      have g_range {x : ℤ} : x ∈ Set.Icc (23 : ℤ) (199 : ℤ) → g x ∈ Set.Icc 0 Real.pi := by
        rintro ⟨hx, hy⟩
        constructor
        . have : g 23 ≤ g x := g_monotone 23 x (by norm_cast)
          simp [g_23] at this
          exact this
        . have : g x ≤ g 199 := g_monotone x 199 (by norm_cast)
          simp [g_199] at this
          exact this
      have : g x = g y := Real.injOn_cos (g_range hx) (g_range hy) hf
      have : (x : ℝ) = (y : ℝ) := g_inj x y this
      simp at this
      exact this
    symm
    calc
      {y | ∃ x : ℤ, 0 ≤ x ∧ x ≤ 999 ∧ f x = y}.ncard = Nat.card {y | ∃ x : ℤ, 0 ≤ x ∧ x ≤ 999 ∧ f x = y} := by rw [Set.Nat.card_coe_set_eq]
      _ = Nat.card ((fun (x : ℤ) => f ↑x) '' (Finset.Icc (23 : ℤ) (199 : ℤ))) := by rw [f_range hf]
      _ = Nat.card (Finset.Icc (23 : ℤ) (199 : ℤ)) := Nat.card_image_of_injOn f_inj
      _ = Finset.card (Finset.Icc (23 : ℤ) (199 : ℤ)) := by rw [Nat.card_eq_finsetCard]
      _ = 177 := by simp