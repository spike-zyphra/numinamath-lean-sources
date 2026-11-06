import Mathlib
open Mathlib

/--
Given a [rational number](https://artofproblemsolving.com/wiki/index.php/Rational_number), write it as a [fraction](https://artofproblemsolving.com/wiki/index.php/Fraction) in lowest terms and calculate the product of the resulting [numerator](https://artofproblemsolving.com/wiki/index.php/Numerator) and [denominator](https://artofproblemsolving.com/wiki/index.php/Denominator). For how many rational numbers between $0$ and $1$ will $20_{}^{}!$ be the resulting [product](https://artofproblemsolving.com/wiki/index.php/Product)? -/

-- This is the algorithm to compute the answer
def count (a : ℕ) : ℚ :=
  match a with
  | 0 => 0
  | n + 1 => if Nat.Coprime n 30 then mkRat n 30 + count n else count n

lemma numbertheory_702 (s : Finset ℚ) (h : ∀ x, x ∈ s ↔ x.den = 30 ∧ 0 < x ∧ x < 10) : ∑ x ∈ s, x = 400 := by
  -- Generalize the lemma statement to use the algorithm
  have sub : ∀ (a : ℕ) (s : Finset ℚ) (h : ∀ x, x ∈ s ↔ x.den = 30 ∧ 0 < x ∧ x < mkRat a 30), ∑ x ∈ s, x = count a := by
    intros a
    induction' a with a ih <;> intros s h
    · norm_num at h
      apply Finset.sum_eq_zero
      intros x hx
      have := (h x).1 hx
      linarith
    · by_cases h0 : a = 0
      · rw [h0]
        rw [h0] at h
        norm_num
        norm_num at h
        rw [(by decide : count 1 = 0)]
        apply Finset.sum_eq_zero
        intros q h1
        cases' (h q).1 h1 with h2 h3
        cases' h3 with h3 h4
        have stp := Rat.mul_den_eq_num q
        rw [h2] at stp
        norm_num at stp
        have stpw : q * 30 < 1 := by linarith
        apply Rat.zero_of_num_zero
        rw [stp] at stpw
        have : q.num < 1 := by qify; linarith
        rw [← Rat.num_pos] at h3
        linarith
      rw [count, ← Finset.sum_filter_add_sum_filter_not _ (fun x => x = mkRat a 30)]
      rw [ih (Finset.filter (fun x => ¬x = mkRat (↑a) 30) s)]
      · by_cases hh : Nat.Coprime a 30
        · have singleton : (Finset.filter (fun x => x = mkRat a 30) s = { mkRat a 30}) := by
            ext b
            constructor
            · intro c
              have := Finset.mem_filter.1 c
              rw [this.2]
              simp
            · intro c
              apply Finset.mem_filter.2
              constructor
              · have d := Finset.mem_singleton.1 c
                rw [d]
                apply (h _).2
                constructor
                · have := Rat.divInt_ofNat a 30
                  norm_num at this
                  rw [← this, Rat.den_mk, if_neg (by decide), Int.gcd_def]
                  norm_num
                  rw [Nat.coprime_iff_gcd_eq_one] at hh
                  rw [hh]
                · have := Rat.divInt_ofNat a 30
                  norm_num at this
                  rw [← this]
                  have := Rat.divInt_ofNat (a + 1) 30
                  norm_num at this
                  norm_num
                  rw [← this]
                  constructor
                  · rw [Nat.coprime_iff_gcd_eq_one] at hh
                    rw [← Rat.num_pos, Rat.num_mk, Int.gcd_def]
                    norm_num
                    rw [hh]
                    norm_num
                    rw [(by decide : Int.sign 30 = 1)]
                    norm_num
                    cases' Nat.eq_or_lt_of_le (Nat.zero_le a) with gg gg <;> tauto
                  · rw [Rat.divInt_eq_div, Rat.divInt_eq_div]
                    norm_num
                    linarith
              · apply Finset.mem_singleton.1
                exact c
          rw [if_pos hh, singleton, Finset.sum_singleton]
        · rw [if_neg hh, Finset.sum_eq_zero]
          · ring
          intros x hx
          have := Finset.mem_filter.1 hx
          cases' this with g1 g2
          have ss := (h _).1 g1
          have := Rat.divInt_ofNat a 30
          norm_num at this
          rw [← this] at g2
          cases' ss with ss sss
          rw [g2, Rat.den_mk, if_neg (by decide), Int.gcd_def] at ss
          norm_num at ss
          rw [Nat.coprime_iff_gcd_eq_one] at hh
          have eq0 : ¬a.gcd 30 = 0 := by
            intro ed0
            rw [Nat.gcd_eq_zero_iff] at ed0
            rw [(by decide : (30 = 0) = False)] at ed0
            tauto
          have qed : ∀ (a : ℕ), a ≠ 0 → a ≠ 1 → 2 ≤ a := by
            intros aa haa haw
            cases' aa with aa aa
            · exfalso; apply haa; decide
            cases' aa with aa aa
            · exfalso; apply haw; decide
            linarith
          have ge := qed _ eq0 hh
          have := @Nat.div_lt_self 30 (a.gcd 30) (by decide) (by linarith)
          linarith
      · intro x
        constructor
        · intro hx
          rw [Finset.mem_filter] at hx
          have := (h _).1 hx.1
          constructor
          · tauto
          constructor
          · tauto
          rw [Rat.mkRat_eq_div]
          norm_num
          rw [Rat.mkRat_eq_div] at this
          norm_num at this
          cases' this with aa a1
          cases' a1 with a2 a1
          have wo : x * ↑(30 : ℕ) < (↑a + 1) := by qify; linarith
          rw [← aa, Rat.mul_den_eq_num] at wo
          apply (by qify; intro als; linarith : x * ↑(30 : ℕ) < ↑a → x < ↑a / 30)
          rw [← aa, Rat.mul_den_eq_num]
          rw [Rat.mkRat_eq_div] at hx
          norm_num at hx
          have gaa : (↑x.num : ℚ) ≠ ↑a := by
            intro aad
            rw [← Rat.mul_den_eq_num, aa] at aad
            norm_num at aad
            rw [← @div_left_inj' _ _ (x * 30 : ℚ) (↑a : ℚ) 30 (by decide)] at aad
            have : x * 30 / 30 = x := by aesop
            rw [this] at aad
            tauto
          have naa : x.num < ↑a + 1 := by qify; linarith
          rw [Int.lt_add_one_iff] at naa
          cases' lt_or_eq_of_le naa with alw nsk
          · qify at *; linarith
          exfalso; apply gaa
          qify at *; linarith
        · intro hx
          rw [Finset.mem_filter]
          constructor
          · apply (h _).2
            constructor
            · tauto
            constructor
            · tauto
            rw [Rat.mkRat_eq_div]
            norm_num
            rw [Rat.mkRat_eq_div] at hx
            norm_num at hx
            cases' hx with aa a1
            cases' a1 with a2 a1
            have wo : x * ↑(30 : ℕ) < (↑a + 1) := by qify; linarith
            rw [← aa, Rat.mul_den_eq_num] at wo
            
            apply (by qify; intro als; linarith : x * ↑(30 : ℕ) < ↑a + 1 → x < (↑a + 1) / 30)
            rw [← aa, Rat.mul_den_eq_num]
            exact wo
          · linarith
  have := sub 300
  norm_num at this
  rw [(by native_decide : count 300 = 400)] at this
  apply this
  assumption