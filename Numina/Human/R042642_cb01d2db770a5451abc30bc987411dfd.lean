import Mathlib

open Finset Nat Pointwise

/-- What is the smallest positive integer with six positive odd integer divisors and twelve positive
even integer divisors? -/
theorem number_theory_54581 :
    IsLeast {n : ℕ | (n.divisors.filter Odd).card = 6 ∧ (n.divisors.filter Even).card = 12} 180 := by

  -- We will use several facts related to prime factorizations. The first is that if a number is
  -- written in the form $2^a \cdot m$ where $m$ is odd, then the number of $2$ factors in it
  -- is $a$.
  have factorization_two_of_two_pow_mul_odd {n a m : ℕ} (hm : Odd m) (hn : n = 2^a * m) :
      n.factorization 2 = a := by
    rw [hn, Nat.factorization_mul (by simp) (ne_of_odd_add hm),
        Nat.Prime.factorization_pow (by norm_num), Finsupp.add_apply, Finsupp.single_eq_same,
        add_right_eq_self]
    apply Nat.factorization_eq_zero_of_not_dvd
    apply Odd.not_two_dvd_nat
    exact hm

  -- Next, the odd divisors of $2^a \cdot m$ is precisely the odd divisors of $m$.
  have odd_divisors_two_pow_mul_odd (a : ℕ) {m : ℕ} (hm : Odd m) :
      (2^a * m).divisors.filter Odd = m.divisors := by
    ext d
    simp
    constructor
    · rintro ⟨⟨hdam, hm1⟩, hd⟩
      refine ⟨?_, hm1⟩
      apply (Coprime.dvd_mul_left _).mp hdam
      apply Coprime.pow_right
      apply coprime_two_right.mpr hd
    · rintro ⟨hdam, hm1⟩
      refine ⟨⟨?_, hm1⟩, ?_⟩
      · apply Dvd.dvd.mul_left hdam
      · exact Odd.of_dvd_nat hm hdam

  -- Finally, the even divisors of $2^a \cdot m$ is precisely the odd divisors of $m$ times $2^i$
  -- for some $i$ with $1 \leq i \leq a$.
  have even_divisors_two_pow_mul_odd (a : ℕ) {m : ℕ} (hm : Odd m) :
      (2^a * m).divisors.filter Even = (image (fun i ↦ 2^i) (Icc 1 a)) * m.divisors := by
    ext d
    simp [mem_mul]
    constructor
    · rintro ⟨⟨hdam, hm1⟩, hd⟩

      have hd2 : d ≠ 0 := by
        contrapose! hm1
        suffices 2^a * m = 0 by simpa using this
        rw [←zero_dvd_iff] at hm1 ⊢
        calc _ ∣ d := by assumption
             _ ∣ _ := by assumption

      rcases exists_eq_two_pow_mul_odd (n := d) hd2 with ⟨a', m', hm', hda'm'⟩

      have factorization_le_factorization_of_dvd {n m : ℕ} (h1 : n ∣ m) (h2 : m ≠ 0) :
          n.factorization 2 ≤ m.factorization 2 := by
        have hn : n ≠ 0 := by
          rintro rfl
          apply h2
          rwa [←zero_dvd_iff]
        apply Finsupp.le_def.mp
        apply (factorization_le_iff_dvd hn h2).mpr h1

      have ha'a : a' ≤ a := by
        calc _ = d.factorization 2 := (factorization_two_of_two_pow_mul_odd hm' hda'm').symm
             _ ≤ (2^a * m).factorization 2 := factorization_le_factorization_of_dvd hdam (by simp [hm1])
             _ = a := factorization_two_of_two_pow_mul_odd hm rfl

      have ha'1 : 1 ≤ a' := by
        calc _ = (2).factorization 2 := by symm; apply Nat.Prime.factorization_self (p := 2) (by norm_num)
             _ ≤ d.factorization 2 := by apply factorization_le_factorization_of_dvd (by rwa [←even_iff_two_dvd]) hd2
             _ = a' := by apply factorization_two_of_two_pow_mul_odd hm' hda'm'

      refine ⟨a', ⟨ha'1, ha'a⟩, m', ⟨?_, hm1⟩, hda'm'.symm⟩

      apply (Coprime.dvd_mul_left (m := 2^(a - a')) _).mp
      · rcases hdam with ⟨k, hamdk⟩
        refine ⟨k, ?_⟩
        suffices 2^a' * (2^(a - a') * m) = 2^a' * (m' * k) from by simpa using this
        rw [←mul_assoc, mul_comm (2^a'), Nat.pow_sub_mul_pow 2 ha'a, ←mul_assoc, ←hda'm', hamdk]
      · apply Coprime.pow_right
        apply coprime_two_right.mpr
        exact hm'

    · rintro ⟨a', ⟨ha'1, ha'a⟩, m', ⟨hm'm, hm1⟩, hda'm'⟩
      refine ⟨⟨?_, hm1⟩, ?_⟩
      · rcases hm'm with ⟨k, hm'mk⟩
        refine ⟨2^(a - a') * k, ?_⟩
        rw [←hda'm', ←mul_comm m', mul_assoc, ←mul_assoc (2^a'), mul_comm (2^a'),
            Nat.pow_sub_mul_pow 2 ha'a, hm'mk, ←mul_assoc, ←mul_comm m', mul_assoc]
      · rw [even_iff_exists_two_mul, ←pow_one 2]
        refine ⟨2^(a' - 1) * m', ?_⟩
        rw [←hda'm', ←mul_assoc, mul_comm (2^1), Nat.pow_sub_mul_pow 2 ha'1]


  -- Now, let's proceed with the proof of the problem. Let $s$ be the set of nonnegative integers
  -- with six positive odd integer divisors and twelve positive even integer divisors. We want to
  -- show that $180$ is the smallest element of $s$.
  set s := {n : ℕ | (n.divisors.filter Odd).card = 6 ∧ (n.divisors.filter Even).card = 12}

  -- Let $t$ be the set of nonnegative odd integers with six divisors.
  set t := {m : ℕ | Odd m ∧ m.divisors.card = 6}

  -- Consider the multiplication by $4$ map.
  let f : ℕ → ℕ := fun m ↦ 4 * m

  -- This map is strictly monotone.
  have f_strict_mono : StrictMono f := by intro m₁ m₂ h; simp [f, h]

  -- We claim that it is a bijection from $t$ to $s$.
  have f_bijOn : Set.BijOn f t s := by
    refine ⟨?_, ?_, ?_⟩
    -- To that end, first we will show that $f$ maps $t$ to $s$. Let $m ∈ t$.
    · rintro m ⟨hm1, hm2⟩
      refine ⟨?_, ?_⟩
      -- Odd divisors of $4m$ is precisely the odd divisors of $m$. So, $4m$ has $6$ odd divisors.
      · rw [←hm2]
        congr 1
        apply odd_divisors_two_pow_mul_odd 2 hm1
      -- Even divisors of $4m$ are precisely the odd divisors of $m$ times $2$ or $4$. So, $4m$ has
      -- $12$ even divisors.
      · suffices ((image (fun i ↦ 2^i) (Icc 1 2)) * m.divisors).card = 12 from ?_
        · rw [←this]
          congr 1
          apply even_divisors_two_pow_mul_odd 2 hm1
        · rw [card_mul_iff.mpr, card_image_iff.mpr (by simp [Set.InjOn]), card_Icc, hm2]
          simp [Set.InjOn]
          rintro _ m₁ a₁ ha₁ ha₁a rfl hm₁m hm2 _ m₂ a₂ ha₂ ha₂a rfl hm₂m hm2 h
          have hm₁1 : Odd m₁ := Odd.of_dvd_nat hm1 hm₁m
          have hm₂1 : Odd m₂ := Odd.of_dvd_nat hm1 hm₂m
          suffices a₁ = a₂ by simpa [this] using h
          calc _ = (2^a₁ * m₁).factorization 2 := (factorization_two_of_two_pow_mul_odd hm₁1 rfl).symm
              _ = (2^a₂ * m₂).factorization 2 := by rw [h]
              _ = _ := factorization_two_of_two_pow_mul_odd hm₂1 rfl

    -- $f$ is obviously injective.
    · apply Set.injOn_of_injective
      apply StrictMono.injective
      apply f_strict_mono

    -- Lastly, we will show that $f$ is surjective. Let $n ∈ s$.
    · rintro n ⟨hn1, hn2⟩

      -- $n$ is nonzero because anything is a divisor of $0$.
      have : n ≠ 0 := by rintro rfl; contradiction
      -- Write $n = 2^a \cdot m$ for some positive integers $a$ and odd integer $m$.
      rcases exists_eq_two_pow_mul_odd this with ⟨a, m, hm1, hnam⟩

      -- Odd divisors of $n$ are precisely the divisors of $m$. So, $m$ has $6$ divisors.
      have hm2 : m.divisors.card = 6 := by
        rw [←hn1, hnam]
        congr 1
        symm
        apply (odd_divisors_two_pow_mul_odd a hm1)

      refine ⟨m, ⟨hm1, hm2⟩, ?_⟩

      -- Therefore, it is enough to show that $a = 2$ to conclude $n = 4m$.
      suffices a = 2 by rw [hnam, this]; rfl

      -- Even divisors of $n$ are precisely the odd divisors of $m$ times $2^i$ for some $i$ with
      -- $1 \leq i \leq a$. There are $12$ even divisors of $n$, $6$ divisors of $m$ and $a$ such
      -- $i$'s. This gives us $a = 2$.
      rw [hnam, even_divisors_two_pow_mul_odd a hm1, card_mul_iff.mpr,
          card_image_iff.mpr (by simp [Set.InjOn]), card_Icc, hm2] at hn2; omega
      simp [Set.InjOn]
      rintro _ m₁ a₁ ha₁ ha₁a rfl hm₁m hm2
      rintro _ m₂ a₂ ha₂ ha₂a rfl hm₂m hm2
      rintro h
      have hm₁ : Odd m₁ := Odd.of_dvd_nat hm1 hm₁m
      have hm₂ : Odd m₂ := Odd.of_dvd_nat hm1 hm₂m
      suffices a₁ = a₂ by simpa [this] using h
      calc _ = (2^a₁ * m₁).factorization 2 := by apply (factorization_two_of_two_pow_mul_odd hm₁ rfl).symm
           _ = (2^a₂ * m₂).factorization 2 := by rw [h]
           _ = _ := by apply factorization_two_of_two_pow_mul_odd hm₂ rfl

  -- Now that we know that $f$ is a monotone bijection from $t$ to $s$, we can conclude that
  -- $180 = f(45)$ is the smallest element of $s$ provided that $45$ is the smallest element of $t$.
  suffices IsLeast t 45 from ?_
  · convert Monotone.map_isLeast f_strict_mono.monotone this
    apply (Set.BijOn.image_eq f_bijOn).symm

  -- Now, we reduced the problem to showing that $45$ is the smallest element of $t$, so we can
  -- forget anything not related to $t$.
  clear! s f

  -- It is clear that $45 \in t$.
  have ht : 45 ∈ t := by decide

  -- Because $t$ is nonempty, it has a smallest element. Call this element $m$.
  let m := Nat.find ⟨45, ht⟩
  have hm1 : IsLeast t m := by
    refine ⟨?_, ?_⟩
    · apply Nat.find_spec ⟨45, ht⟩
    · intro n hn1
      apply Nat.find_le hn1
  clear_value m
  rw [IsLeast.isLeast_iff_eq hm1]
  rcases hm1 with ⟨hm, hm1⟩
  simp [lowerBounds] at hm1

  -- By definition of $t$, $m$ is odd and it has $6$ divisors.
  have hm2 : Odd m := by simp [t] at hm; exact hm.1
  have hm3 : m.divisors.card = 6 := by simp [t] at hm; exact hm.2

  -- Because $45 \in t$, $m \leq 45$.
  have hm4 : m ≤ 45 := hm1 ht

  -- $m$ is not $0$ because anything is a divisor of $0$.
  have hm5 : m ≠ 0 := by rintro rfl; contradiction

  -- $m$ is not $1$ because the only divisor of $1$ is $1$.
  have hm6 : m ≠ 1 := by rintro rfl; contradiction

  -- Because $m$ is not $0$ or $1$, it has at least one prime factor.
  by_cases hm7 : m.primeFactors.card = 0
  · rw [Finset.card_eq_zero, primeFactors_eq_empty] at hm7
    rcases hm7 with (rfl | rfl) <;> contradiction

  -- For contradiction, assume that $m$ has a single prime factor.
  by_cases hm8 : m.primeFactors.card = 1
  · exfalso
    -- Write $m = p^a$ for some prime $p$ and positive integer $a$.
    rcases Finset.card_eq_one.mp hm8 with ⟨p, hmp⟩
    let a := m.factorization p
    have hmpa : m = p^a := by
      rw [←factorization_prod_pow_eq_self hm5, prod_factorization_eq_prod_primeFactors, hmp,
          Finset.prod_singleton]

    -- On the one hand, the number of divisors of $m$ is $a + 1$ and on the other hand, it is $6$.
    -- So, $a = 5$.
    have ha : a = 5 := by
      suffices 6 = a + 1 from by omega
      rw [←hm3, card_divisors hm5, hmp, Finset.prod_singleton]
    clear_value a
    subst ha

    -- However, $p$ is an odd prime number, so $p \geq 3$. Therefore, $m \geq 3^5 > 45$ which is a
    -- contradiction.
    suffices 3^5 ≤ m from by omega
    suffices 3 ≤ p by rw [hmpa]; gcongr
    by_contra!
    interval_cases p
    · contradiction
    · contradiction
    · rw [hmpa] at hm2; contradiction

  -- Now, let's show thot $m$ has actually two prime factors.
  replace hm7 : m.primeFactors.card = 2 := by
    -- We already now that $m$ has at least two prime factors, so it suffices to show that it has
    -- at most two prime factors.
    suffices m.primeFactors.card ≤ 2 from by omega

    -- Notice that $6$ cannot be written as a product of more than two integers greater than $1$.
    have prod_eq_six {s : Finset ℕ} {f : ℕ → ℕ}  (h1 : ∀ x ∈ s, f x ≠ 1) (h2 : ∏ x ∈ s, f x = 6) :
      s.card ≤ 2 := by

      have h3 : ∀ x ∈ s, 2 ≤ f x:= by
        intro x hx
        by_contra!
        interval_cases hfx : (f x)
        · suffices 0 = 6 from by omega
          calc _ = f x * ∏ y ∈ s \ {x}, f y := by simp [hfx]
              _ = ∏ y ∈ ({x} ∪ s \ {x}), f y := by rw [prod_union (by simp), prod_singleton]
              _ = ∏ y ∈ s, f y := by congr; simp [hx]
              _ = _ := by rw [h2]
        · exact h1 x hx hfx

      by_contra!
      rcases exists_subset_card_eq (s := s) (n := 3) (by omega) with ⟨t, hts, ht⟩
      rcases card_eq_three.mp ht with ⟨a, b, c, hab, hac, hbc, htabc⟩

      have : ∏ x ∈ s, f x = (∏ x ∈ t, f x) * (∏ x ∈ s \ t, f x) := by
        calc _ = ∏ x ∈ t ∪ (s \ t), f x := by congr; simp [hts]
            _ = _ := by rw [prod_union]; apply disjoint_sdiff

      suffices 8 ≤ ∏ x ∈ s, f x from ?_
      · rw [h2] at this
        contradiction

      calc _ = 2 * 2 * 2 := by rfl
          _ ≤ f a * f b * f c := by gcongr;
                                    · apply h3
                                      apply hts
                                      simp [htabc]
                                    · apply h3
                                      apply hts
                                      simp [htabc]
                                    · apply h3
                                      apply hts
                                      simp [htabc]
            _ = ∏ x ∈ t, f x := by rw [htabc, prod_insert (by simp [hab, hac]), prod_pair hbc, mul_assoc]
            _ ≤ ∏ x ∈ s, f x := by apply le_of_dvd (by simp; intro i hi; linarith [h3 i hi])
                                   apply prod_dvd_prod_of_subset t s f hts

    -- This follows from the fact that $6$ cannot be written as a product of more than two integers
    -- greater than $1$, and the number of divisors formula for $m$.
    apply prod_eq_six (f := fun x ↦ (m.factorization x) + 1)
    · intro p hp
      suffices 0 < m.factorization p by omega
      apply Nat.Prime.factorization_pos_of_dvd _ hm5 _
      · exact (mem_primeFactors.mp hp).1
      · exact (mem_primeFactors.mp hp).2.1
    · rw [←card_divisors hm5, hm3]

  -- Write $m = p^a \cdot q^b$ for some positive integers $a$ and $b$ and prime numbers $p < q$.
  rcases Finset.card_eq_two.mp hm7 with ⟨p, q, hpq, hmpq⟩
  wlog hpq2 : p < q generalizing p q
  · apply this q p hpq.symm _ (by omega)
    rw [hmpq, pair_comm]

  let a := m.factorization p
  let b := m.factorization q

  have hmpa : m = p^a * q^b := by
    rw [←factorization_prod_pow_eq_self hm5, prod_factorization_eq_prod_primeFactors, hmpq,
        prod_pair hpq]

  have hp1 : p.Prime := by exact (mem_primeFactors (n := m).mp (by simp [hmpq])).1
  have hp2 : p ∣ m := by exact (mem_primeFactors (n := m).mp (by simp [hmpq])).2.1
  have hp3 : Odd p := by apply Odd.of_dvd_nat hm2 hp2
  have hp4 : 3 ≤ p := by by_contra!; interval_cases p <;> contradiction
  have hq1 : q.Prime := by exact (mem_primeFactors (n := m).mp (by simp [hmpq])).1
  have hq2 : q ∣ m := by exact (mem_primeFactors (n := m).mp (by simp [hmpq])).2.1
  have hq3 : Odd q := by apply Odd.of_dvd_nat hm2 hq2
  have ha1 : 1 ≤ a := by apply Nat.Prime.factorization_pos_of_dvd hp1 hm5 hp2
  have hb1 : 1 ≤ b := by apply Nat.Prime.factorization_pos_of_dvd hq1 hm5 hq2

  -- Using the number of divisors formula for $m$, we get $(a + 1) \cdot (b + 1) = 6$.
  have hab1 : (a + 1) * (b + 1) = 6 := by
    rw [←hm3, card_divisors hm5, hmpq, prod_pair hpq]
  clear_value a b

  -- This equation has two solutions: $(a, b) = (1, 2)$ and $(a, b) = (2, 1)$.
  have hab2 : (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) := by
    have : (a + 1) ∈ ({1, 2, 3, 6} : Finset ℕ) := by
      exact mem_divisors (m := 6).mpr ⟨⟨b + 1, by rw [hab1]⟩, (by norm_num)⟩
    simp at this
    rcases this with (rfl | rfl | rfl | rfl) <;> omega

  -- Let $m_1 = p^1 \cdot q^2$ and $m_2 = p^2 \cdot q^1$.
  let m₁ := p^1 * q^2
  let m₂ := p^2 * q^1

  -- $m_2$ is in $t$ because it is odd and it has $6$ divisors.
  have hm₂ : m₂ ∈ t := by
    refine ⟨?_, ?_⟩
    · rw [Nat.odd_mul]
      refine ⟨?_, by convert hq3; simp⟩
      apply Odd.pow
      exact hp3
    · simp [m₂]
      rw [card_divisors (by simp [Nat.Prime.ne_zero hp1, Nat.Prime.ne_zero hq1]),
          primeFactors_mul (by simp [Nat.Prime.ne_zero hp1]) (by simp [Nat.Prime.ne_zero hq1]),
          primeFactors_pow _ (by norm_num), Nat.Prime.primeFactors hp1, Nat.Prime.primeFactors hq1,
          prod_union (by simp [Disjoint, hpq]), prod_singleton, prod_singleton,
          Nat.factorization_mul (by simp [Nat.Prime.ne_zero hp1]) (by simp [Nat.Prime.ne_zero hq1]),
          Nat.Prime.factorization_pow hp1, Finsupp.add_apply, Finsupp.add_apply,
          Nat.Prime.factorization hq1, Finsupp.single_eq_same, Finsupp.single_eq_same,
          Finsupp.single_eq_of_ne hpq, Finsupp.single_eq_of_ne hpq.symm, add_zero, zero_add]; rfl

  -- Because $p < q$, we have $m_2 < m_1$.
  have hm₂m₁ : m₂ < m₁ := by
    calc _ = p^2 * q^1 := by rfl
         _ = p * q * p := by ring
         _ < p * q * q := by gcongr; nlinarith
         _ = p^1 * q^2 := by ring
         _ = m₁ := by rfl

  -- Therefore, $m = m₂$
  have hm8 : m = m₂ := by
    rcases hab2 with (⟨ha2, hb2⟩ | ⟨ha2, hb2⟩)
    · suffices m₁ < m₁ by omega
      calc _ = m := by simp [m₁, hmpa, ha2, hb2]
           _ ≤ m₂ := by apply hm1 hm₂
           _ < _ := by exact hm₂m₁
    · simp [m₂, hmpa, ha2, hb2]
  simp [m₂] at hm8

  -- Finally, it is enough to show that $p = 3$ and $q = 5$.
  suffices p = 3 ∧ (p = 3 → q = 5) by rw [hm8, this.1, this.2 this.1]; rfl

  refine ⟨?_, ?_⟩
  -- For a contradiction, assume that $p \neq 3$.
  · contrapose! hm4
    -- Then, $q > p \geq 5$. However, $m \le 45$. This is a contradiction.
    have : 5 ≤ p := by exact Nat.Prime.five_le_of_ne_two_of_ne_three hp1 (by omega) hm4
    calc _ < 5^3 := by norm_num
         _ = 5^2 * 5^1 := by rfl
         _ ≤ p^2 * q^1 := by gcongr; omega
         _ = m := by simp [hm8]

  -- Now, let's show that $q = 5$. We know that $p = 3$ and $5 ≤ q$. From $m \le 45$, we get $q ≤ 5$
  -- and hence $q = 5$.
  · intro hp4
    have : 5 ≤ q := by exact Nat.Prime.five_le_of_ne_two_of_ne_three hq1 (by omega) (by omega)
    suffices q ≤ 5 by omega
    nlinarith