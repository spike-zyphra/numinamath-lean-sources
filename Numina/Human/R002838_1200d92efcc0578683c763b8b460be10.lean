import Mathlib

-- we show a simple lemma to write a postive rational number as a fraction of two positive integers
lemma pos_rat_exist (r: ℚ) (h: 0 < r): ∃ n m: ℤ, 0 < n ∧ 0 < m ∧ r = (n: ℚ) / m := by
    use r.num, r.den
    simp [h]
    constructor
    .
        apply Rat.den_pos
    .
        symm
        exact Rat.num_div_den r

/- For a non-empty set M⊂Q, the following two conditions are satisfied:
1.if a∈M and b∈M, then a+b∈M and ab∈M;
2.if r∈Q, then exactly one of the following three statements is true:
r∈M,−r∈M,r=0.
Prove that the set M coincides with the set of all positive rational numbers.-/

theorem number_theory_120171 (M : Set ℚ)
    (h1 : ∀ a ∈ M, ∀ b ∈ M, a + b ∈ M ∧ a * b ∈ M)
    (h2 : ∀ r: ℚ, ((r ∈ M) ∧ (-r ∉ M) ∧ (r ≠ 0)) ∨ ((-r ∈ M) ∧ (r ∉ M) ∧ (r ≠ 0)) ∨
    ((r = 0) ∧ (r ∉ M) ∧ (-r ∉ M))):
    M = {x: ℚ | 0 < x} := by

    have f0: 0 ∉ M := by
        specialize h2 0
        simp at h2
        exact h2

    -- then we write h2 in a more usable form
    replace h2: ∀ r: ℚ, r ≠ 0 → (r ∈ M) ∧ (-r ∉ M) ∨ (-r ∈ M) ∧ (r ∉ M) := by
        intro r hr
        specialize h2 r
        simp [hr] at h2
        rcases h2 with r0 | r0
        .
            left
            tauto
        .
            right
            tauto

    -- we first show that 1 ∈ M
    have f1: 1 ∈ M := by
        by_contra! o
        specialize h2 1 (by norm_num)
        simp [o] at h2
        specialize h1 (-1) h2 (-1) h2
        norm_num at h1
        simp [o] at h1

    -- then we can show that ∀ n: ℤ, 0 < n → n ∈ M
    have fn: ∀ n: ℤ, 0 < n → ↑n ∈ M := by
        intro n hn
        set m:= n.natAbs
        have o: (n: ℚ) = (m: ℚ) := by
            simp [m]
            rw [Int.cast_natAbs]
            rw [show |n| = n by apply abs_of_nonneg; omega]
        rw [o]
        clear o
        replace hn: 0 < m := by
            simp [m]
            omega
        clear_value m
        induction' m with m ih
        .
            simp at hn
        .
            by_cases r: m = 0
            .
                simp [r]
                tauto
            .

                rw [show ↑(m + (1: ℕ)) = ↑m + (1: ℚ) by simp]
                have u: 0 < m := by omega
                simp [u] at ih
                specialize h1 (↑m) ih 1 (by tauto)
                tauto

    -- then we can show that ∀ m, 1 / m ∈ M
    have fm: ∀ m: ℤ, 0 < m → (1: ℚ) / ↑m ∈ M := by
        intro m hm
        by_contra! o
        have i:= h2
        specialize h2 ((1: ℚ) / ↑m)
        simp at h2
        have v: ¬ m = 0 := by
            omega
        simp [v] at h2
        field_simp at h2
        rcases h2 with h2 | h2
        .
            rcases h2 with ⟨f, g⟩
            tauto
        .
            rcases h2 with ⟨f, g⟩

            -- then we have -1 = (1 / ↑m) * (-m) ∈ M
            specialize fn m hm
            specialize h1 (-(1: ℚ) / ↑m) f m fn
            rcases h1 with ⟨j, k⟩
            field_simp at k
            specialize i 1 (by norm_num)
            tauto

    -- finally, we obtain that n / m ∈ ℚ
    have f: ∀ n m: ℤ, 0 < n → 0 < m → (↑n / (m: ℚ)) ∈ M := by
        intro n m hn hm
        specialize fn n hn
        specialize fm m hm
        specialize h1 (↑n) fn ((1: ℚ) / ↑m) fm
        field_simp at h1
        tauto

    -- write f in a better way
    replace f: ∀ r: ℚ, 0 < r → r ∈ M := by
        intro r hr
        have j:= pos_rat_exist r hr
        obtain ⟨n, m, hn, hm, r_eq⟩ := j
        simp [r_eq]
        specialize f n m hn hm
        tauto


    -- at last, we show the set equality
    ext x
    constructor

    -- the forward direction
    .
        intro h
        simp
        by_contra! l
        specialize h2 x
        by_cases v: x = 0
        .
            simp [v] at h
            tauto
        .
            simp [v] at h2
            replace v: x < 0 := by
                by_contra! o
                replace o: x = 0 := by linarith
                simp [o] at v
            specialize f (-x) (by linarith)
            simp [f] at h2
            tauto


    -- the backward direction
    .
        intro h
        simp at h
        specialize f x (by linarith)
        tauto