import Mathlib


/- For any positive rational number $x$, it can be uniquely expressed as $x = \frac{p}{q}$, where $p$ and $q$ are positive integers with $\text{gcd}(p, q) = 1$. Consider a function $f$ defined on the positive rational numbers by \[f\left(\frac{p}{q}\right) = \begin{cases} \frac{pq}{2} & \text{if } p \text{ or } q \text{ is even} \\ p + q & \text{otherwise} \end{cases}.\] Determine the number of values of $x$ such that $0 < x < 1$ and $f(x) = 10$. -/
theorem number_theory_613635
  (f : ℚ → ℕ)
  (hf : ∀ p q : ℕ, p > 0 → q > 0 → p.Coprime q →
    f (p / q: ℚ) = if (Even p ∨ Even q) then (p * q / 2) else p + q) :
  {x : ℚ | 0 < x ∧ x < 1 ∧ f x = 10}.ncard = 4 := by

  -- four pairs in total: (1,20), (4,5), (1,9), (3,7)
  suffices {x : ℚ | 0 < x ∧ x < 1 ∧ f x = 10} =
    {1/20, 4/5, 1/9, 3/7} by
    rw [this]
    norm_num

  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]

  constructor
  · rintro ⟨xgt, xlt, fxeq⟩
    have h1: x.num.toNat = x.num := by
      refine Int.toNat_of_nonneg ?_
      exact Rat.num_nonneg.mpr xgt.le
    have h2: x = x.num.toNat / x.den := by
      qify at h1
      rw [h1, Rat.num_div_den]
    have h3: x.num.toNat.Coprime x.den := by
      lift x to NNRat using xgt.le
      norm_cast
      exact NNRat.coprime_num_den x
    have h4: 0 < x.num.toNat := by
      suffices 0 < x.num by
        exact Int.lt_toNat.mpr this
      exact Rat.num_pos.mpr xgt
    have h5 := Rat.den_pos x
    specialize hf x.num.toNat x.den h4 h5 h3
    rw [h2] at fxeq
    rw [fxeq] at hf

    -- consider whether x.num and x.den are both odd or some is even.
    by_cases hx: Even x.num.toNat ∨ Even x.den
    · rw [if_pos hx] at hf
      replace hf: x.num.toNat * x.den = 20 := by
        have: x.num.toNat * x.den =
          2 * (x.num.toNat * x.den / 2) := by
          refine Eq.symm (Nat.two_mul_div_two_of_even ?_)
          exact Nat.even_mul.mpr hx
        rw [this, ← hf]
      -- two positive coprime number multiply to 20, first < second,
      -- only two pairs: (1,20), (4,5)
      suffices (x.num.toNat = 1 ∧ x.den = 20) ∨ (x.num.toNat = 4 ∧ x.den = 5) by
        rcases this with hh | hh
        <;> rw [h2] <;> simp [hh]
      rw [h2] at xlt
      generalize x.num.toNat = p at h4 hf h3 xlt ⊢
      generalize x.den = q at h5 hf h3 xlt ⊢
      have pdvd: p ∣ 20 := Dvd.intro q hf
      have ple: p ≤ 20 := Nat.le_of_dvd (by norm_num) pdvd
      have co_p: p.Coprime (20/p) := by
        rwa [← hf, Nat.mul_div_right q h4]
      have plt: p < q := by
        qify at h5 ⊢
        rwa [div_lt_one h5] at xlt
      have peq: p = 1 ∨ p = 2 ∨ p = 4 := by
        have: q = 20 / p := by
          rw [← hf]
          exact Eq.symm (Nat.mul_div_right q h4)
        rw [this] at plt
        clear * - h4 ple plt pdvd
        revert pdvd plt h4
        revert ple p
        decide
      rcases peq with peq | peq | peq
      · left
        simp only [peq, one_mul] at hf
        simp [peq, hf]
      · rw [peq] at co_p
        absurd co_p
        norm_num
      · rw [peq] at hf
        right
        clear * - peq hf
        omega

    · -- both are odd case.
      rw [if_neg hx] at hf
      push_neg at hx
      simp only [Nat.not_even_iff_odd] at hx
      -- two odd numbers add to 10, first < second, only two possible solutions are (1,9), (3,7).
      rw [h2] at xlt
      suffices (x.num.toNat = 1 ∧ x.den = 9) ∨
        (x.num.toNat = 3 ∧ x.den = 7) by
        rw [h2]
        rcases this with hh | hh
        <;> simp [hh]
      generalize x.num.toNat = p at h4 hf hx xlt ⊢
      generalize x.den = q at h5 hf hx xlt ⊢
      have plt: p < q := by
        qify at h5 ⊢
        rwa [div_lt_one h5] at xlt
      have peq: p = 1 ∨ p = 3 := by
        have: q = 10 - p := by
          simp [hf]
        rw [this] at plt
        replace plt: p < 5 := by omega
        replace := hx.left
        revert this h4
        revert plt
        clear * -
        decide +revert
      rcases peq with peq | peq
      <;> rw [peq] at hf ⊢
      · left; omega
      · right; omega

  · -- verification
    rintro (xeq | xeq | xeq | xeq)
    <;> norm_num [xeq]
    · have: (1/20:ℚ) = ↑(1:ℕ) / ↑(20:ℕ) := by simp
      rw [this, hf 1 20]
      <;> norm_num
      exact Nat.even_iff.mpr rfl
    · have: (4/5:ℚ) = ↑(4:ℕ) / ↑(5:ℕ) := by simp
      rw [this, hf 4 5]
      <;> norm_num
      intro h
      absurd h
      exact Nat.not_odd_iff.mpr rfl
    · have: (1/9:ℚ) = ↑(1:ℕ) / ↑(9:ℕ) := by simp
      rw [this, hf 1 9]
      <;> norm_num
      exact Nat.odd_iff.mpr rfl
    · have: (3/7:ℚ) = ↑(3:ℕ) / ↑(7:ℕ) := by simp
      rw [this, hf 3 7]
      <;> norm_num