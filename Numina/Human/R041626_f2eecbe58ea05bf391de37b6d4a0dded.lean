import Mathlib

open Polynomial

/-
Determine all positive integers $n$ for which there exists a polynomial $P_n(x)$ of degree $n$ with
integer coefficients that is equal to $n$ at $n$ different integer points and that equals zero at zero.
-/

theorem algebra_23623 :
    { n : ℕ | n ≥ 1 ∧ ∃ p : ℤ[X], p.degree = n ∧ p.eval 0 = 0 ∧
      ∃ x : ℕ → ℤ, Set.InjOn x (Set.Icc 1 n) ∧ ∀ i ∈ Set.Icc 1 n, p.eval (x i) = n  } = Set.Icc 1 4 := by
  ext n
  constructor
  swap
  -- At least one solution exist for each n ∈ {1, 2, 3, 4}
  . intro h
    simp only [Set.mem_Icc] at h
    constructor
    exact h.1
    replace h : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
    rcases h with h | h | h | h
    -- for n = 1, choose P(x) = x with x = 1
    . subst h
      use X
      split_ands
      . simp
      . simp
      . use λ _ => 1; simp
    -- for n = 2, choose P(x) = 2x^2 with x = +1, -1
    . subst h
      use 2 * X ^ 2
      split_ands
      . simp
        have : degree (2 : ℤ[X]) = 0 := by apply degree_C; simp
        simp [this]
      . simp
      . use λ | 1 => 1 | 2 => -1 | _ => 0
        split_ands
        . intro i hi j hj
          simp at hi hj
          replace hi : i = 1 ∨ i = 2 := by omega
          replace hj : j = 1 ∨ j = 2 := by omega
          rcases hi with hi | hi <;> rcases hj with hj | hj <;> simp [hi, hj]
        . intro i hi
          simp at hi
          replace h : i = 1 ∨ i = 2 := by omega
          rcases h with h | h <;> simp [h]
    -- for n = 3, choose P(x) = x^3 + 3x^2 - x with x = +1, -1, -3
    . subst h
      use X ^ 3 + 3 * X ^ 2 - X
      split_ands
      . suffices (X ^ 3 + 3 * X ^ 2 - X : ℤ[X]).support = {1, 2, 3} from by simp [degree, this]; norm_cast
        ext k
        have h : k = 1 ∨ k = 2 ∨ k = 3 ∨ (k ≠ 1 ∧ k ≠ 2 ∧ k ≠ 3) := by omega
        rcases h with h | h | h | h <;> (simp [h, coeff_X]; try omega)
      . simp
      . use λ | 1 => 1 | 2 => -1 | 3 => -3 | _ => 0
        split_ands
        . intro i hi j hj
          simp at hi hj
          replace hi : i = 1 ∨ i = 2 ∨ i = 3 := by omega
          replace hj : j = 1 ∨ j = 2 ∨ j = 3 := by omega
          rcases hi with hi | hi | hi <;> rcases hj with hj | hj | hj <;> simp [hi, hj]
        . intro i hi
          simp only [Set.mem_Icc] at hi
          replace h : i = 1 ∨ i = 2 ∨ i = 3 := by omega
          rcases h with h | h | h <;> simp [h]
    -- for n = 4, choose P(x) = -x^4 + 5x^2 with x = 1, -1, 2, -2
    . subst h
      use -X ^ 4 + 5 * X ^ 2
      split_ands
      . suffices (-X ^ 4 + 5 * X ^ 2 : ℤ[X]).support = {2, 4} from by simp [degree, this]; norm_cast
        ext k
        have h : k = 2 ∨ k = 4 ∨ (k ≠ 2 ∧ k ≠ 4) := by omega
        rcases h with h | h | h <;> (simp [h, coeff_X]; try omega)
      . simp
      . use λ | 1 => 1 | 2 => -1 | 3 => 2 | 4 => -2 | _ => 0
        split_ands
        . intro i hi j hj
          simp at hi hj
          replace hi : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
          replace hj : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
          rcases hi with hi | hi | hi | hi <;> rcases hj with hj | hj | hj | hj <;> simp [hi, hj]
        . intro i hi
          simp at hi
          replace h : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
          rcases h with h | h | h | h <;> simp [h]
  . intro ⟨n_gt_0, p, deg_p, p_0, ⟨x, inj_x, p_x_eq_n⟩⟩
    simp only [Set.mem_Icc]

    -- let q = p - n in ℤ[X], and show that q's roots are the xi's.
    let q := p - n
    have q_x_eq_0 : ∀ i ∈ Set.Icc 1 n, q.eval (x i) = 0 := by
      intro i hi
      simp [q, p_x_eq_n i hi]
    have degree_q : q.degree = n := by
      calc
      _ = p.degree := by
        apply degree_sub_eq_left_of_degree_lt
        have : degree (n : ℤ[X]) = 0 := by apply degree_C; linarith
        simp [this, deg_p]
        linarith
      _ = _ := deg_p
    have natDegree_q : q.natDegree = n := by simp [natDegree, degree_q]; rfl
    have q_ne_0 : q ≠ 0 := by intro h; simp [h] at degree_q
    have q_roots : q.roots = (Multiset.Icc 1 n).map x := by
      apply (Multiset.eq_of_le_of_card_le _ _).symm
      . apply (Multiset.le_iff_subset _).mpr
        . intro c hc
          simp only [Multiset.mem_map, Multiset.mem_Icc] at hc
          obtain ⟨i, hi, hi'⟩ := hc
          subst hi'
          simp [q_ne_0, q_x_eq_0 i (by simpa using hi)]
        . rw [Multiset.nodup_map_iff_of_inj_on (by simpa [Set.InjOn] using inj_x)]
          exact Multiset.nodup_Icc
      . calc
        _ ≤ q.natDegree := q.card_roots'
        _ = n := natDegree_q
        _ = _ := by simp [Multiset.Icc]
    have q_0 : eval 0 q = -n := by simp [q, p_0]
    have card_q_roots : Multiset.card q.roots = n := by simp [q_roots, Multiset.Icc]
    have leadingCoeff_q_ne_0 : q.leadingCoeff ≠ 0 := by
      intro h
      rw [leadingCoeff_eq_zero] at h
      contradiction

    -- Decompose q in ℚ[X] as it is of degree n, and has n roots.
    let q' := q.map (Int.castRingHom ℚ)
    have degree_q' : q'.degree = n := by
      calc
      _ = q.degree := by simp [q', ne_or_eq]
      _ = _ := degree_q
    have natDegree_q' : q'.natDegree = n := by simp [natDegree, degree_q']; rfl
    have q'_ne_0 : q' ≠ 0 := by intro h; simp [h] at degree_q'
    have q'_roots : q'.roots = ((Multiset.Icc 1 n).map (x . : ℕ → ℚ)) := by
      apply (Multiset.eq_of_le_of_card_le _ _).symm
      . apply (Multiset.le_iff_subset _).mpr
        . intro c hc
          simp at hc
          obtain ⟨i, hi, hi'⟩ := hc
          subst hi'
          simp [q'_ne_0, q', q_x_eq_0 i (by simpa using hi)]
        . rw [Multiset.nodup_map_iff_of_inj_on (by simpa [Set.InjOn] using inj_x)]
          exact Multiset.nodup_Icc
      . calc
        _ ≤ q'.natDegree := q'.card_roots'
        _ = n := natDegree_q'
        _ = _ := by simp [Multiset.Icc]
    have splits_q' : Splits (RingHom.id ℚ) q' := by
      apply splits_iff_card_roots.mpr
      simp [q'_roots, natDegree_q', Multiset.Icc]
    have q'_decomp := q'.eq_prod_roots_of_splits_id splits_q'

    -- Going back to ℤ[X] we can thus write  -n = q.leadingCoeff * ∏ i ∈ Finset.Icc 1 n, -x i
    have q_decomp : q = C q.leadingCoeff * (Multiset.map (fun a => X - C a) q.roots).prod := by
      apply map_injective (Int.castRingHom ℚ) (RingHom.injective_int _)
      rw [Polynomial.map_mul, map_C, Polynomial.map_multiset_prod, q_roots]
      rw [leadingCoeff_map' (RingHom.injective_int _)] at q'_decomp
      rw [q'_roots] at q'_decomp
      simpa using q'_decomp
    clear! q'
    have h1 : -n = q.leadingCoeff * ∏ i ∈ Finset.Icc 1 n, -x i := by
      have := q_decomp
      apply congrArg (eval 0 .) at this
      simp only [eval_mul, eval_multiset_prod] at this
      simpa [card_q_roots, q_roots, Multiset.Icc, q_0]

    -- Apply magnitudes to get n = |q.leadingCoeff| * ∏ i ∈ Finset.Icc 1 n, |x i|
    replace h1 : n = |q.leadingCoeff| * ∏ i ∈ Finset.Icc 1 n, |x i| := by
      have := h1
      apply congrArg (|.|) at this
      rw [abs_mul] at this
      rw [Finset.abs_prod] at this
      simpa [abs_neg, Nat.abs_cast]

    -- Show that |x_i| ≥ 2 for n - 2 different values of i, as x_i ∈ {1,-1} happens at most twice.
    have (k) : ∃ j ∈ Finset.Icc 1 n, ∀ i ∈ Finset.Icc 1 n, i ≠ j → x i ≠ k := by
      by_cases h : ∃ i1 ∈ Finset.Icc 1 n, x i1 = k
      . obtain ⟨i1, h1, h2⟩ := h
        use i1
        split_ands
        exact h1
        intro i hi
        have := inj_x (by simpa using hi) (by simpa using h1)
        omega
      . push_neg at h
        use 1
        split_ands
        simp [n_gt_0]
        intro i hi
        have := h i hi
        omega
    obtain ⟨i1, hi1, hi1'⟩ := this 1
    obtain ⟨i2, hi2, hi2'⟩ := this (-1)
    have hxi_ne_0 : ∀ i ∈ Finset.Icc 1 n, x i ≠ 0 := by
      intro i hi h
      have := p_x_eq_n i (by simpa using hi)
      rw [h, p_0] at this
      omega
    have h2 : ∀ i ∈ Finset.Icc 1 n \ {i1, i2}, |x i| ≥ 2 := by
      intro k hk
      by_contra h
      have hk : k ∈ Finset.Icc 1 n ∧ k ≠ i1 ∧ k ≠ i2 := by simpa using hk
      let ⟨hk1, hk2, hk3⟩ := hk
      replace h : |x k| ≤ 1 := by omega
      replace h := abs_le.mp h
      replace h : x k = 0 ∨ x k = 1 ∨ x k = -1 := by omega
      have := hxi_ne_0 k (by simpa using hk1)
      have := hi1' k (by simpa using hk1) hk2
      have := hi2' k (by simpa using hk1) hk3
      omega
    have i1_i2_sub : {i1, i2} ⊆ Finset.Icc 1 n := by
      intro i hi
      replace hi : i = i1 ∨ i = i2 := by simpa using hi
      simp at hi1 hi2 ⊢
      omega

    -- Deduce the following inequality : n ≥ 2^(n - 2)
    replace h1 : (n : ℤ) ≥ 2 ^ (n - 2) := by
      calc
      (n : ℤ) = |q.leadingCoeff| * (∏ i ∈ Finset.Icc 1 n \ {i1, i2}, |x i|) * ∏ i ∈ {i1, i2}, |x i| := by
        rw [←Finset.prod_sdiff i1_i2_sub] at h1
        linarith
      _ ≥ 1 * (∏ i ∈ Finset.Icc 1 n \ {i1, i2}, 2) * ∏ i ∈ {i1, i2}, 1 := by
        have : ∏ i ∈ Finset.Icc 1 n \ {i1, i2}, |x i| ≥ ∏ i ∈ Finset.Icc 1 n \ {i1, i2}, 2 := by
          apply Finset.prod_le_prod
          omega
          exact h2
        have : ∏ i ∈ {i1, i2}, |x i| ≥ ∏ i ∈ {i1, i2}, 1 := by
          apply Finset.prod_le_prod
          omega
          intro i hi
          by_contra h
          push_neg at h
          replace h : |x i| ≤ 0 := Int.lt_add_one_iff.mp h
          replace h := abs_le.mp h
          replace h : x i = 0 := by omega
          have := hxi_ne_0 i
          replace hi : i = i1 ∨ i = i2 := by simpa using hi
          simp at hi1 hi2
          have := this (by simp; omega)
          omega
        have : |q.leadingCoeff| ≥ 1 := by
          by_contra h
          replace h : |q.leadingCoeff| ≤ 0 := by omega
          replace h := abs_le.mp h
          replace h : q.leadingCoeff = 0 := by omega
          simp only [leadingCoeff_eq_zero, q] at h
          contradiction
        gcongr
      _ ≥ 1 * 2 ^ (n - 2) * 1 := by
        have : ∏ i ∈ Finset.Icc 1 n \ {i1, i2}, (2 : ℤ) = 2 ^ (n - 1) ∨ ∏ i ∈ Finset.Icc 1 n \ {i1, i2}, (2 : ℤ) = 2 ^ (n - 2) := by
          simp [Finset.card_sdiff i1_i2_sub]
          by_cases h : i1 = i2
          . left
            simp [h]
          . right
            simp [Finset.card_pair h]
        have : ∏ i ∈ Finset.Icc 1 n \ {i1, i2}, (2 : ℤ) ≥ 2 ^ (n - 2) := by
          rcases this with h | h
          rw [h]
          norm_cast
          apply (2).pow_le_pow_of_le (by omega)
          omega
          omega
        have : ∏ i ∈ {i1, i2}, (1 : ℤ) = 1 := by simp
        gcongr
        omega
      _ = _ := by ring_nf

    -- We are now ready to show that 1 ≤ n ≤ 4
    split_ands
    omega
    norm_cast at h1
    -- Show that n ≥ 2^(n - 2) is possible only when n ≤ 4, by induction on n
    by_contra h
    replace h : n ≥ 5 := by omega
    suffices 2 ^ (n - 2) ≥ n + 1 from by omega
    revert h
    generalize n = n
    induction n
    next => omega
    next n ih =>
      intro h
      by_cases hn : n = 4
      . simp [hn]
      . replace hn : n ≥ 5 := by omega
        replace ih := ih hn
        calc
        2 ^ (n + 1 - 2) = 2 ^ (n - 2 + 1) := by apply congrArg (2 ^ .); omega
        _ = 2 ^ (n - 2) * 2 := by rfl
        _ ≥ (n + 1) * 2 := by gcongr
        _ ≥ n + 1 + 1 := by omega
