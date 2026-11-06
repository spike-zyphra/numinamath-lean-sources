import Mathlib


/- A main lemma: if q > 0 and the number of q-tuples of integers whose values are bounded by B are exactly (2B+1)^q. -/
lemma card_functions_of_bounded_vals {q B : ℕ} (hq : q > 0) : Set.ncard {x : Fin q → ℤ | ∀ i, |x i| ≤ B} = (2 * B + 1) ^ q := by
  -- prove by induction on q
  induction q, hq using Nat.le_induction
  · -- q=1 => count [-B, B]
    simp
    have : (Finset.Icc (-B : ℤ) B).card = 2 * B + 1 := by
      simp
      norm_cast
      ring
    have : Set.ncard (Finset.Icc (-B : ℤ) B : Set ℤ) = 2 * B + 1 := by
      rw [Set.ncard_coe_Finset]
      exact this
    rw [←this]
    let f (x : Fin 1 → ℤ) (_ : x ∈ {x | ∀ (i : Fin 1), |x i| ≤ ↑B}) := x 0
    apply Set.ncard_congr f
    · intro x hx
      simp at hx
      simp [f]
      exact abs_le.mp (hx 0)
    · intro _ _ _ _ heq
      simp [f] at heq
      ext i
      fin_cases i
      simp [heq]
    · intro b hb
      simp at hb
      use ![b]
      constructor
      · simp [f]
      · simp
        exact abs_le.mpr hb
  · -- case q + 1: we show that this set is in bijection with the cartesian product of the set of integers in [-B, B] and the set of q-tuples of integers whose values are bounded by B
    -- Then apply the induction hypothesis, we are done.
    rename_i q hq ih
    have ih : Nat.card {x : Fin q → ℤ | ∀ (i : Fin q), |x i| ≤ ↑B} = (2 * B + 1) ^ q := by exact ih
    let t := Finset.Icc (-B : ℤ) B × {x : Fin q → ℤ | ∀ (i : Fin q), |x i| ≤ ↑B}
    have ht : Nat.card t = (2 * B + 1) ^ (q + 1) := by
      simp only [t]
      rw [Nat.card_prod, Nat.card_eq_fintype_card, ih, Nat.pow_add_one']
      simp
      norm_cast
      ring
    suffices h : Nat.card {x :  Fin (q + 1) → ℤ| ∀ (i : Fin (q + 1)), |x i| ≤ ↑B} = (2 * B + 1) ^ (q + 1)
    · exact h
    · rw [←ht]
      apply Nat.card_congr
      have hx0_le (x : {x :  Fin (q + 1) → ℤ| ∀ (i : Fin (q + 1)), |x i| ≤ ↑B}) : x.1 0 ∈ Finset.Icc (-B : ℤ) B := by
        obtain ⟨x, hx⟩ := x
        simp at hx ⊢
        exact abs_le.mp (hx 0)
      have hxtail (x : {x :  Fin (q + 1) → ℤ| ∀ (i : Fin (q + 1)), |x i| ≤ ↑B}) : Fin.tail x.1 ∈ {x : Fin q → ℤ | ∀ (i : Fin q), |x i| ≤ ↑B} := by
        obtain ⟨x, hx⟩ := x
        simp at hx ⊢
        intro i
        simp [Fin.tail]
        apply hx
      let f (x : {x :  Fin (q + 1) → ℤ | ∀ (i : Fin (q + 1)), |x i| ≤ ↑B}) : t := (⟨x.1 0, hx0_le x⟩, ⟨Fin.tail x.1, hxtail x⟩)
      apply Equiv.ofBijective f
      constructor
      · intro ⟨x₁, hx₂⟩ ⟨x₂, hx₂⟩ hf
        simp [f] at hf
        apply Prod.ext_iff.mp at hf
        simp at hf
        apply Subtype.val_inj.mp
        simp
        rw [←Fin.cons_self_tail x₁, ←Fin.cons_self_tail x₂]
        rw [hf.1, hf.2]
      · intro ⟨⟨x0, h0⟩, ⟨xtail, htail⟩⟩
        let x : Fin (q + 1) → ℤ := Fin.cons x0 xtail
        have hx : x ∈ {x : Fin (q + 1) → ℤ | ∀ (i : Fin (q + 1)), |x i| ≤ ↑B} := by
          simp [x]
          intro i
          rcases Fin.eq_zero_or_eq_succ i with hi | hi
          · simp [hi]
            simp at h0
            exact abs_le.mpr h0
          · obtain ⟨j, hi⟩ := hi
            rw [hi, Fin.cons_succ]
            simp at htail
            apply htail
        use ⟨x, hx⟩
        simp [f]
        apply Prod.ext
        all_goals simp [x]

/- 5. (NET 3) ${ }^{\mathrm{IMO} 5}$ Let a set of $p$ equations be given,  $$ \begin{gathered} a_{11} x_{1}+\cdots+a_{1 q} x_{q}=0 \\ a_{21} x_{1}+\cdots+a_{2 q} x_{q}=0 \\ \vdots \\ a_{p 1} x_{1}+\cdots+a_{p q} x_{q}=0, \end{gathered} $$  with coefficients $a_{i j}$ satisfying $a_{i j}=-1,0$, or +1 for all $i=1, \ldots, p$ and $j=1, \ldots, q$. Prove that if $q=2 p$, there exists a solution $x_{1}, \ldots, x_{q}$ of this system such that all $x_{j}(j=1, \ldots, q)$ are integers satisfying $\left|x_{j}\right| \leq q$ and $x_{j} \neq 0$ for at least one value of $j$. -/
theorem algebra_25093 {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (a : Fin p → Fin q → ℤ) (ha : ∀ i j, a i j = -1 ∨ a i j = 0 ∨ a i j = 1)
    (h : q = 2 * p) :
    ∃ x : Fin q → ℤ, (∀ i, ∑ j : Fin q, a i j * x j = 0) ∧ (∀ j, |x j| ≤ q) ∧ ∃ j, x j ≠ 0 := by

  -- let evak denote the evaluation of the linear form defined by the coefficients a
  let eval (x : Fin q → ℤ) : Fin p → ℤ := fun i => ∑ j : Fin q, a i j * x j

  -- let S denote all the functions from Fin q to ℤ whose values are bounded by p
  let S : Set (Fin q → ℤ) := {x | ∀ i , |x i| ≤ p}

  -- let T denote all the functions from Fin p to ℤ whose values are bounded by p * q
  let T : Set (Fin p → ℤ) := {x | ∀ i, |x i| ≤ p * q}

  -- apply the main lemma to S and T, we obtain that S has (2 * p + 1) ^ q elements and T has (2 * (p * q) + 1) ^ p elements
  have hcard_S : S.ncard = (2 * p + 1) ^ q := by
    apply card_functions_of_bounded_vals
    exact hq

  obtain ⟨s, hs⟩ : ∃ s : Finset (Fin q → ℤ), s = S := by
    refine Set.Finite.exists_finset_coe ?_
    apply Set.finite_of_ncard_pos
    simp [hcard_S]

  have hcard_s : s.card = (2 * p + 1) ^ q := by
    rw [←hcard_S, ←hs]
    exact Eq.symm (Set.ncard_coe_Finset s)

  have hcard_T : T.ncard = (2 * (p * q) + 1) ^ p := by
    apply card_functions_of_bounded_vals
    exact hp

  obtain ⟨t, ht⟩ : ∃ t : Finset (Fin p → ℤ), t = T := by
    refine Set.Finite.exists_finset_coe ?_
    apply Set.finite_of_ncard_pos
    simp [hcard_T]

  have hcard_t : t.card = (2 * (p * q) + 1) ^ p := by
    rw [←hcard_T, ←ht]
    exact Eq.symm (Set.ncard_coe_Finset t)

  -- Obviously, |S| > |T|
  have hcard_lt_card : t.card * 1 < s.card := by
    simp [hcard_s, hcard_t]
    rw [h, pow_mul, add_sq]
    gcongr
    ring_nf
    simp [hp]

  -- Note that the eval function maps every x ∈ S to an element of T
  have heval : ∀ x ∈ s, eval x ∈ t := by
    intro x hx
    have hx : x ∈ S := by
      rw [←hs]
      exact hx
    simp [S] at hx
    suffices h : eval x ∈ T
    · rw [←ht] at h
      exact h
    · simp [T, eval]
      intro i
      trans ∑ j : Fin q, |a i j * x j|
      · exact Finset.abs_sum_le_sum_abs (fun i_1 ↦ a i i_1 * x i_1) Finset.univ
      trans ∑ j : Fin q, |x j|
      · apply Finset.sum_le_sum
        intro j _
        rcases ha i j with h | h | h
        all_goals simp [h]
      trans ∑ _ : Fin q, p
      · apply Finset.sum_le_sum
        intro j _
        exact hx j
      · simp
        apply le_of_eq
        ring

  -- Therefore, we can apply the pigeonhole principle to obtain two elements x₁ x₂ ∈ S such that eval x₁ = eval x₂
  obtain ⟨y, hy, hlt⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to heval hcard_lt_card

  obtain ⟨x₁, hx₁, x₂, hx₂, hne⟩ := Finset.one_lt_card.mp hlt
  simp at hx₁ hx₂
  obtain ⟨hle₁, heval₁⟩ := hx₁
  obtain ⟨hle₂, heval₂⟩ := hx₂
  have hle₁ : x₁ ∈ S := by
    rw [←hs]
    exact hle₁
  have hle₂ : x₂ ∈ S := by
    rw [←hs]
    exact hle₂
  simp [S] at hle₁ hle₂

  -- We are done by verifying x₁ - x₂ satisfies the conditions of the problem
  use x₁ - x₂
  split_ands
  · -- The first condition is equvalent to eval x₁ - x₂ = y - y =0
    intro i
    simp [mul_sub]
    change eval x₁ i - eval x₂ i = 0
    simp [heval₁, heval₂]
  · -- The second condition is equivalent to |x₁ j - x₂ j| ≤ q for all j
    -- Since |x₁ j| ≤ p and |x₂ j| ≤ p, we have |x₁ j - x₂ j| ≤ |x₁ j| + |x₂ j| ≤ 2p = q
    intro j
    simp
    trans |x₁ j| + |x₂ j|
    · exact abs_sub (x₁ j) (x₂ j)
    · trans p + p
      · gcongr
        · apply hle₁
        · apply hle₂
      · simp [h]
        apply le_of_eq
        ring
  · -- The last condition is equivalent to x₁ j ≠ x₂ j for at least one j
    -- If x₁ j = x₂ j for all j, then we have x₁ = x₂, which is a contradiction
    by_contra hne
    simp at hne
    have : x₁ = x₂ := by
      ext i
      apply sub_eq_zero.mp
      apply hne
    contradiction
