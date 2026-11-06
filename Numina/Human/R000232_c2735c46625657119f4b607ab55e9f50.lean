import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

/-
  The following fractions are written on the board  $\frac{1}{n},
  \frac{2}{n-1}, \frac{3}{n-2}, \ldots , \frac{n}{1}$  where  $n$  is a natural number.
   Vasya calculated the differences of the neighboring fractions in this row and found among them  $10000$
  fractions of type  $\frac{1}{k}$  (with natural  $k$ ).
  Prove that he can find even  $5000$  more of such these differences.
-/
theorem number_theory_8640 (n : ℕ) (hn : 0 < n) (f : ℕ → ℚ) (hf : f = λ x : ℕ ↦ (x + (1 : ℚ)) / (n - x))
  (hcardge : {i | i < n - 1 ∧ ∃ k : ℕ, f (i + 1) - f i = 1 / k}.ncard ≥ 10000) : {i | i < n - 1 ∧ ∃ k : ℕ, f (i + 1) - f i = 1 / k}.ncard ≥ 10000 + 5000 := by

  -- apply the chinese_Remainder theorem to find a solution of n + 1 ∣ s * (s - 1)
  have chinese_remainder (a b : ℕ) (ha : a > 1) (hb : b > 1) (hab : Coprime a b) : ∃ s, s ≡ 0 [MOD a] ∧ s ≡ 1 [MOD b] ∧ a * b ∣ s * (s - 1) ∧ s > 1 ∧ s < a * b := by
    let z := Nat.chineseRemainder hab 0 1
    have hz : z = Nat.chineseRemainder hab 0 1 := by exact rfl
    have ⟨s, ⟨h1, h2⟩⟩ := z
    have hs : s ≥ 1 := by
      by_contra hlt
      simp at hlt
      rw [hlt] at h2
      have : b = 1 := by
        refine eq_one_of_dvd_one ?_
        exact dvd_of_mod_eq_zero (id (ModEq.symm h2))
      simp [this] at hb
    have hs' : s > 1 := by
      by_contra hle
      push_neg at hle
      rcases lt_or_eq_of_le hle with h | h
      · linarith
      · simp [h] at h1
        have : a = 1 := by
          refine eq_one_of_dvd_one ?_
          exact dvd_of_mod_eq_zero h1
        simp [this] at ha
    use s
    split_ands
    · exact h1
    · exact h2
    · have hb : b ∣ s - 1 := by exact (modEq_iff_dvd' hs).mp (id (ModEq.symm h2))
      have ha : a ∣ s := by exact dvd_of_mod_eq_zero h1
      exact Nat.mul_dvd_mul ha hb
    · exact hs'
    · obtain h := Nat.chineseRemainder_lt_mul hab 0 1 (not_eq_zero_of_lt ha) (not_eq_zero_of_lt hb)
      simp [<-hz] at h
      exact h

  -- if x ∣ s * (s - 1), then decompose x into x₁ x₂ such that gcd x₁ x₂ = 1
  have decomposition (x s x1 x2 : ℕ) (hs : s ≥ 1) (hx : x ∣ s * (s - 1)) (hx1 : x1 = x.gcd s) (hx2 : x2 = x.gcd (s - 1)) : x = x1 * x2 ∧ Coprime x1 x2 := by
    have hco : Coprime s (s - 1) := by
      refine (coprime_self_sub_right hs).mpr ?_
      exact Nat.gcd_one_right s
    constructor
    · simp [hx1, hx2]
      apply Eq.symm
      apply (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hco).mpr
      exact hx
    · rw [hx1, hx2]
      exact Coprime.gcd_both x x hco

  -- count the card of x.divisors d such that d x/d are coprime
  have card_of_coprime (x : ℕ) (hx : x > 0) : (Finset.filter (fun d => Coprime d (x / d)) x.divisors).card = 2 ^ x.primeFactors.card := by
    induction x using Nat.recOnPosPrimePosCoprime
    · -- if x = p ^n for some n > 0, then {1, p^n}.card = 2 ^1 holds
      rename_i p n hp hn
      -- prove rhs = 2 ^ 1
      have : (p ^ n).primeFactors = {p} := by
        refine primeFactors_prime_pow ?hk hp
        exact not_eq_zero_of_lt hn
      simp [this]
      -- prove lhf = {1, p ^n}.card
      have : (Finset.filter (fun d => Coprime d (p ^ n / d)) (p ^ n).divisors) = {1, p ^ n} := by
        apply Finset.ext
        intro d
        constructor
        · intro hd
          simp at hd
          obtain ⟨⟨h1, _⟩, h2⟩ := hd
          obtain ⟨k, ⟨hle, heq⟩⟩ := (Nat.dvd_prime_pow hp).mp h1
          rw [heq, Nat.pow_div hle] at h2
          · by_cases hkeq0 : k = 0
            · simp [hkeq0] at heq
              simp [heq]
            · have : k ≥ 1 := by exact one_le_iff_ne_zero.mpr hkeq0
              apply (Nat.coprime_pow_left_iff this _ _).mp at h2
              by_cases hkeqn : k = n
              · simp [hkeqn] at heq
                simp [heq]
              · have : k < n := by exact Nat.lt_of_le_of_ne hle hkeqn
                have : n - k > 0 := by exact zero_lt_sub_of_lt this
                apply (Nat.coprime_pow_right_iff this _ _).mp at h2
                simp at h2
                simp [h2, Nat.Prime] at hp
          · exact Prime.pos hp
        · intro hd
          simp at hd
          rcases hd with hd | hd <;> simp [hd]
          · have : p ≠ 0 := by exact Nat.Prime.ne_zero hp
            exact fun a ↦ False.elim (this a)
          · constructor
            · have : p ≠ 0 := by exact Nat.Prime.ne_zero hp
              exact fun a ↦ False.elim (this a)
            · rw [Nat.div_self]
              exact Nat.gcd_one_right (p ^ n)
              exact hx
      -- prove {1, p ^ n} = 2, i.e., 1 ≠ p ^ n
      rw [this]
      refine Finset.card_pair ?_
      have : p ^ n > 1 := by
        calc
          p ^ n > p ^ 0 := by refine (Nat.pow_lt_pow_iff_right ?_).mpr hn; exact Prime.one_lt hp
          _ = 1 := by simp
      exact Nat.ne_of_lt this
    · -- prove if x = 0 => contradiction
      linarith
    · -- prove if x = 1 => {1}.card = 2 ^ 0
      simp
      exact rfl
    · -- prove if x = a * b and coprime a b, then ...
      rename_i a b ha hb hco iha ihb
      -- rhs : prove 2 ^ (a * b).primeFactors.card = 2 ^ a.primeFactors.card * 2 ^ b.primeFactors.card
      have rhs_simp : (a * b).primeFactors = a.primeFactors ∪ b.primeFactors := by
        exact Coprime.primeFactors_mul hco
      have rhs_disj : Disjoint a.primeFactors b.primeFactors := by
        exact Coprime.disjoint_primeFactors hco
      rw [rhs_simp, Finset.card_union_of_disjoint rhs_disj]
      -- lhs : prove lhs ≃ lhs of case a × lhs of case b by constructing a bijection
      have lhs_simp : Finset.filter (fun d ↦ d.Coprime (a * b / d)) (a * b).divisors ≃
          Finset.product (Finset.filter (fun d ↦ d.Coprime (a / d)) a.divisors) (Finset.filter (fun d ↦ d.Coprime (b / d)) b.divisors) := by
        -- explicitly construct f
        let f : Finset.product (Finset.filter (fun d ↦ d.Coprime (a / d)) a.divisors) (Finset.filter (fun d ↦ d.Coprime (b / d)) b.divisors)
            → Finset.filter (fun d ↦ d.Coprime (a * b / d)) (a * b).divisors :=
            fun x =>
              let ⟨⟨x1, x2⟩, hx⟩ := x
              have hx1 : x1 ∈ Finset.filter (fun d ↦ d.Coprime (a / d)) a.divisors := by
                apply Finset.mem_product.mp at hx
                exact hx.left
              have hx2 : x2 ∈ Finset.filter (fun d ↦ d.Coprime (b / d)) b.divisors := by
                apply Finset.mem_product.mp at hx
                exact hx.right
              have : x1 * x2 ∈ Finset.filter (fun d ↦ d.Coprime (a * b / d)) (a * b).divisors := by
                simp at hx1 hx2 ⊢
                obtain ⟨⟨hx1dvd, hx1pos⟩, hx1co⟩ := hx1
                obtain ⟨⟨hx2dvd, hx2pos⟩, hx2co⟩ := hx2
                split_ands
                · exact Nat.mul_dvd_mul hx1dvd hx2dvd
                · exact hx1pos
                · exact hx2pos
                · have : a * b / (x1 * x2) = a / x1 * (b / x2) := by
                    rw [Nat.div_mul_div_comm]
                    · exact hx1dvd
                    · exact hx2dvd
                  rw [this]
                  apply Coprime.mul_right <;> apply Coprime.mul
                  · exact hx1co
                  · have : x2.Coprime a := by
                      refine Coprime.coprime_dvd_left hx2dvd ?_
                      · exact coprime_comm.mp hco
                    exact Coprime.coprime_div_right this hx1dvd
                  · have : x1.Coprime b := by
                      exact Coprime.coprime_dvd_left hx1dvd hco
                    exact Coprime.coprime_div_right this hx2dvd
                  · exact hx2co
              ⟨x1 * x2, this⟩
        apply Equiv.symm
        have hf : Function.Bijective f := by
          constructor
          · -- show f is injective
            intro ⟨d₁, hd₁⟩ ⟨d₂, hd₂⟩ heq
            simp [f] at heq
            apply Finset.mem_product.mp at hd₁
            apply Finset.mem_product.mp at hd₂
            simp at hd₁ hd₂ ⊢
            obtain ⟨⟨⟨hdvd₁₁, hpos₁₁⟩, hco₁₁⟩, ⟨⟨hdvd₁₂, hpos₁₂⟩, hco₁₂⟩⟩ := hd₁
            obtain ⟨⟨⟨hdvd₂₁, hpos₂₁⟩, hco₂₁⟩, ⟨⟨hdvd₂₂, hpos₂₂⟩, hco₂₂⟩⟩ := hd₂
            have : Coprime d₁.1 d₂.2 := by
              apply Coprime.coprime_dvd_left hdvd₁₁
              exact Coprime.coprime_dvd_right hdvd₂₂ hco
            have hdvd : d₁.1 ∣ d₂.1 * d₂.2 := by use d₁.2; rw [heq]
            have h1 : d₁.1 ∣ d₂.1 := by exact Coprime.dvd_of_dvd_mul_right this hdvd
            have h2 : d₂.1 ∣ d₁.1 := by
              apply Coprime.dvd_of_dvd_mul_right
              · apply Coprime.coprime_dvd_left hdvd₂₁
                apply Coprime.coprime_dvd_right hdvd₁₂ hco
              · use d₂.2
            have : d₁.1 = d₂.1 := by apply Nat.dvd_antisymm h1 h2
            simp [this] at heq
            rcases heq with h | h
            · exact Prod.ext this h
            · simp [h] at hdvd₂₁
              contradiction
          · -- show f is surjective
            intro ⟨x, hx⟩
            let d₁ := x.gcd a
            let d₂ := x.gcd b
            simp at hx
            obtain ⟨⟨hxdvd, hxpos⟩, hxco⟩ := hx
            have hxeq : x = d₁ * d₂ := by
              simp [d₁, d₂]
              apply Eq.symm
              exact (gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hco).mpr hxdvd
            have hd₁ : d₁ ∈ Finset.filter (fun d ↦ d.Coprime (a / d)) a.divisors := by
              simp
              split_ands
              · exact Nat.gcd_dvd_right x a
              · exact not_eq_zero_of_lt ha
              · simp [d₁]
                have : x.gcd a ∣ x := by exact Nat.gcd_dvd_left x a
                apply Coprime.coprime_dvd_left this
                apply Coprime.coprime_dvd_right ?_ hxco
                refine (div_dvd_iff_dvd_mul ?_ ?hb).mpr ?_
                · exact Nat.gcd_dvd_right x a
                · by_contra heq
                  simp [heq] at this
                  simp [this] at hxdvd
                  have : ¬ (a = 0 ∨ b = 0) := by push_neg; push_neg at hxpos; exact hxpos
                  contradiction
                · use x.gcd a * b / x
                  rw [<-Nat.mul_div_assoc _ hxdvd, <-Nat.mul_div_assoc]
                  ring_nf
                  nth_rw 1 [hxeq]
                  refine Nat.mul_dvd_mul ?_ ?_
                  · exact Nat.dvd_refl d₁
                  · exact Nat.gcd_dvd_right x b
            have hd₂ : d₂ ∈ Finset.filter (fun d ↦ d.Coprime (b / d)) b.divisors := by
              simp
              split_ands
              · exact Nat.gcd_dvd_right x b
              · exact not_eq_zero_of_lt hb
              · simp [d₂]
                have : x.gcd b ∣ x := by exact Nat.gcd_dvd_left x b
                apply Coprime.coprime_dvd_left this
                apply Coprime.coprime_dvd_right ?_ hxco
                refine (div_dvd_iff_dvd_mul ?_ ?_).mpr ?_
                · exact Nat.gcd_dvd_right x b
                · by_contra heq
                  simp [heq] at this
                  simp [this] at hxdvd
                  have : ¬ (a = 0 ∨ b = 0) := by push_neg; push_neg at hxpos; exact hxpos
                  contradiction
                · use x.gcd b * a / x
                  rw [<-Nat.mul_div_assoc _ hxdvd, <-Nat.mul_div_assoc]
                  ring_nf
                  nth_rw 1 [hxeq]
                  rw [mul_comm]
                  refine Nat.mul_dvd_mul ?_ ?_
                  · exact Nat.dvd_refl d₂
                  · exact Nat.gcd_dvd_right x a
            have hd : (d₁, d₂) ∈ (Finset.filter (fun d ↦ d.Coprime (a / d)) a.divisors) ×ˢ Finset.filter (fun d ↦ d.Coprime (b / d)) b.divisors := by
              exact Finset.mk_mem_product hd₁ hd₂
            use ⟨(d₁, d₂), hd⟩
            simp [f]
            exact id (Eq.symm hxeq)
        exact Equiv.ofBijective f hf
      -- then lhs's card = lhs of case a 's card * lhs of case b 's card
      have lhs_card : (Finset.filter (fun d ↦ d.Coprime (a * b / d)) (a * b).divisors).card =
          (Finset.filter (fun d ↦ d.Coprime (a / d)) a.divisors).card * (Finset.filter (fun d ↦ d.Coprime (b / d)) b.divisors).card := by
        rw [<-Finset.card_product]
        exact Eq.symm (Finset.card_eq_of_equiv (id lhs_simp.symm))
      rw [lhs_card]
      -- apply ih
      have ha : a > 0 := by exact zero_lt_of_lt ha
      have hb : b > 0 := by exact zero_lt_of_lt hb
      rw [iha ha, ihb hb]
      simp [Nat.pow_add]


  -- simplify the difference f (i + 1) - f i
  have simplify_f (i k : ℕ) (hi : i + 1 < n) : f (i + 1) - f i = 1 / k ↔ (n + 1) * k = (n - i) * (n - i - 1) := by
    have hrel1 : (n : ℤ) - (i + 1) ≠ (0 : ℤ) := by
      by_contra heq
      have : (n : ℤ) = i + 1 := by linarith
      norm_cast at this
      simp [this] at hi
    have hrel2 : (n : ℤ) - i ≠ (0 : ℤ) := by
      by_contra heq
      have : (n : ℤ) = i := by linarith
      norm_cast at this
      simp [this] at hi
    simp [hf]
    have : (↑i + 1 + 1) / (↑n - (↑i + 1)) - (↑i + (1 : ℚ)) / (↑n - ↑i) =
      (i + 1 + (1 : ℤ)) /. (↑n - (↑i + 1)) - (i + (1 : ℤ)) /. (↑n - ↑i) := by norm_cast
    rw [this]
    rw [Rat.divInt_sub_divInt _ _ hrel1 hrel2]
    rw [Int.add_mul, add_mul, mul_sub, one_mul, add_mul, mul_sub, mul_add, one_mul, mul_one]
    have : ↑i * ↑n - ↑i * ↑i + (↑n - ↑i) + (↑n - ↑i) - (↑i * ↑n - (↑i * ↑i + ↑i) + (↑n - (↑i + 1))) = n + (1 : ℤ) := by
      ring
    rw [this]
    have : (k : ℚ)⁻¹ = 1 /. (k : ℤ) := by norm_cast; field_simp
    rw [this]
    by_cases hk : k = 0
    · simp [hk]
      have : ¬ (n - i = 0 ∨ n - i - 1 = 0) := by
        by_contra h
        rcases h with h | h
        · have : n ≤ i := by exact Nat.le_of_sub_eq_zero h
          have : ¬ n ≤ i := by push_neg; apply Nat.lt_trans (lt_add_one i) hi
          contradiction
        · have : n ≤ i + 1 := by exact Nat.le_of_sub_eq_zero h
          have : ¬ n ≤ i + 1 := by push_neg; exact hi
          contradiction
      simp [this]
      by_contra heq
      have : ((n : ℤ) - (↑i + 1)) * (↑n - ↑i) ≠ 0 := by
        exact Int.mul_ne_zero hrel1 hrel2
      apply Rat.divInt_eq_zero this |>.mp at heq
      norm_cast at heq
    · rw [Rat.divInt_eq_divInt]
      rw [one_mul, <-Nat.cast_sub, <-Nat.cast_one, <-Nat.cast_add, <-Nat.cast_add, <-Nat.cast_sub]
      norm_cast
      rw [Nat.sub_add_eq]
      nth_rw 2 [mul_comm]
      · exact le_of_succ_le hi
      · calc
          i ≤ i + 1 := by exact Nat.le_add_right i 1
          _ ≤ n := by exact le_of_succ_le hi
      · exact Int.mul_ne_zero hrel1 hrel2
      · norm_cast

  -- therefore, {i | i < n - 1 ∧ ∃ k : ℕ, f (i + 1) - f i = 1 / k} ≃ {s | 1 < s ∧ s ≤ n ∧ (n + 1) ∣ s * (s - 1)}
  have congr_solution_dvd : {i | i < n - 1 ∧ ∃ k : ℕ, f (i + 1) - f i = 1 / k} ≃ {s | 1 < s ∧ s ≤ n ∧ (n + 1) ∣ s * (s - 1)} := by
    let g : {i | i < n - 1 ∧ ∃ k : ℕ, f (i + 1) - f i = 1 / k} → {s | 1 < s ∧ s ≤ n ∧ (n + 1) ∣ s * (s - 1)} :=
      fun i =>
        have : n - i ∈ {s | 1 < s ∧ s ≤ n ∧ (n + 1) ∣ s * (s - 1)} := by
          let ⟨i, ⟨hle, hk⟩⟩ := i
          simp
          constructor
          · exact lt_tsub_comm.mp hle
          · obtain ⟨k, hk⟩ := hk
            use k
            apply Eq.symm <| (simplify_f i k ?_).mp hk
            exact add_lt_of_lt_sub hle
        ⟨n - i, this⟩
    have hg : Function.Bijective g := by
      constructor
      · intro ⟨i₁, hi₁⟩ ⟨i₂, hi₂⟩ heq
        simp [g] at heq
        simp at hi₁ hi₂
        obtain ⟨hlt₁⟩ := hi₁
        obtain ⟨hlt₂⟩ := hi₂
        have : n - (i₁ : ℤ) = n - i₂ := by
          rw [<-Nat.cast_sub, <-Nat.cast_sub]
          norm_cast
          · have : i₂ < n := by exact lt_of_lt_pred hlt₂
            exact le_of_succ_le this
          · have : i₁ < n := by exact lt_of_lt_pred hlt₁
            exact le_of_succ_le this
        have : (i₁ : ℤ) = i₂ := by exact (Int.sub_right_inj ↑n).mp this
        norm_cast at this
        simp [this]
      · intro ⟨s, hs⟩
        simp at hs
        obtain ⟨hgt, ⟨hle, hdvd⟩⟩ := hs
        have : n - s ∈ {i | i < n - 1 ∧ ∃ k : ℕ, f (i + 1) - f i = 1 / k} := by
          simp
          constructor
          · exact (tsub_lt_tsub_iff_left_of_le_of_le hle hn).mpr hgt
          · obtain ⟨k, hk⟩ := hdvd
            use k
            let i := n - s
            have hi : n - s = i := by exact rfl
            rw [hi]
            field_simp
            apply (simplify_f i k ?_).mpr
            simp [<-hk, i]
            rw [Nat.sub_sub_self hle]
            simp [i]
            calc
              n - s + 1 < n - 1 + 1 := by
                apply Nat.add_lt_add_right ?_ 1
                exact (tsub_lt_tsub_iff_left_of_le_of_le hle hn).mpr hgt
              _ = n := by rw [Nat.sub_add_cancel hn]
        use ⟨n - s, this⟩
        simp [g]
        exact Nat.sub_sub_self hle
    exact Equiv.ofBijective g hg

  -- prove {s | 1 < s ∧ s ≤ n ∧ (n + 1) ∣ s * (s - 1)} ≃ Finset.filter (fun d => Coprime d ((n + 1) / d)) (n + 1).divisors / {1, n + 1}
  have congr_dvd_divisor : {s | 1 < s ∧ s ≤ n ∧ (n + 1) ∣ s * (s - 1)} ≃ ((Finset.filter (fun d => Coprime d ((n + 1) / d)) (n + 1).divisors).erase 1).erase (n + 1) := by
    let g : {s | 1 < s ∧ s ≤ n ∧ (n + 1) ∣ s * (s - 1)} → ((Finset.filter (fun d => Coprime d ((n + 1) / d)) (n + 1).divisors).erase 1).erase (n + 1) :=
      fun s =>
        have : (n + 1).gcd s ∈ ((Finset.filter (fun d => Coprime d ((n + 1) / d)) (n + 1).divisors).erase 1).erase (n + 1) := by
          obtain ⟨s, ⟨hgt, ⟨hle, hdvd⟩⟩⟩ := s
          simp
          split_ands
          · have : (n + 1).gcd s ≤ s := by refine gcd_le_right s ?_; exact zero_lt_of_lt hgt
            have : (n + 1).gcd s ≤ n := by exact Nat.le_trans this hle
            apply Nat.ne_of_lt
            exact Nat.lt_add_one_iff.mpr this
          · by_contra heq
            have : Coprime (n + 1) s := by exact heq
            have : n + 1 ∣ s - 1 := by exact Coprime.dvd_of_dvd_mul_left heq hdvd
            have : n + 1 ≤ s - 1 := by apply Nat.le_of_dvd ?_ this; exact zero_lt_sub_of_lt hgt
            have : ¬ n + 1 ≤ s - 1 := by
              push_neg
              calc
                s - 1 < s := by exact sub_one_lt_of_lt hgt
                _ ≤ n := by rel [hle]
                _ < n + 1 := by exact lt_add_one n
            contradiction
          · exact Nat.gcd_dvd_left (n + 1) s
          · apply Coprime.coprime_dvd_left (Nat.gcd_dvd_right (n + 1) s)
            have : (n + 1) / (n + 1).gcd s ∣ s - 1 := by
              let k := (n + 1).gcd (s - 1)
              obtain ⟨h⟩ := decomposition (n + 1) s ((n + 1).gcd s) k (one_le_of_lt hgt) hdvd (refl _) (refl _)
              nth_rw 1 [h]
              rw [Nat.mul_div_cancel_left]
              · exact Nat.gcd_dvd_right (n + 1) (s - 1)
              · by_contra heq
                simp at heq
                simp [heq] at h
            apply Coprime.coprime_dvd_right this
            apply coprime_self_sub_right ?_ |>.mp
            · rw [Nat.sub_sub_self]
              · exact Nat.gcd_one_right s
              · exact one_le_of_lt hgt
            · exact sub_le s 1
        ⟨(n + 1).gcd s, this⟩

    have hg : Function.Bijective g := by
      constructor
      · intro ⟨s₁, hs₁⟩ ⟨s₂, hs₂⟩ heq
        simp at hs₁ hs₂
        obtain ⟨hlt₁, ⟨hle₁, hdvd₁⟩⟩ := hs₁
        obtain ⟨hlt₂, ⟨hle₂, hdvd₂⟩⟩ := hs₂
        simp [g] at heq
        let s := (n + 1).gcd s₁
        let t := (n + 1).gcd (s₁ - 1)
        have ⟨hst, hstco⟩ := decomposition (n + 1) s₁ s t (one_le_of_lt hlt₁) hdvd₁ (refl _) (refl _)
        have hst' : n + 1 = s * ((n + 1).gcd (s₂ - 1)) := (decomposition (n + 1) s₂ s ((n + 1).gcd (s₂ - 1)) (one_le_of_lt hlt₂) hdvd₂ heq (refl _)).left
        nth_rw 1 [hst] at hst'
        have ht : t = (n + 1).gcd (s₂ - 1) := by
          apply Nat.mul_right_inj ?_ |>.mp hst'
          by_contra heq
          simp [heq] at hst
        have hmods₁ : s₁ ≡ 0 [MOD s] := by
          apply modEq_zero_iff_dvd.mpr
          exact Nat.gcd_dvd_right (n + 1) s₁
        have hmodt₁ : s₁ ≡ 1 [MOD t] := by
          suffices : 1 ≡ s₁ [MOD t]
          · exact id (ModEq.symm this)
          · apply (modEq_iff_dvd' ?_).mpr
            exact Nat.gcd_dvd_right (n + 1) (s₁ - 1)
            exact one_le_of_lt hlt₁
        have hmods₂ : s₂ ≡ 0 [MOD s] := by
          apply modEq_zero_iff_dvd.mpr
          simp [s, heq]
          exact Nat.gcd_dvd_right (n + 1) s₂
        have hmodt₂ : s₂ ≡ 1 [MOD t] := by
          suffices : 1 ≡ s₂ [MOD t]
          · exact id (ModEq.symm this)
          · apply (modEq_iff_dvd' ?_).mpr
            · rw [ht]
              exact Nat.gcd_dvd_right (n + 1) (s₂ - 1)
            · exact one_le_of_lt hlt₂
        apply Nat.chineseRemainder_modEq_unique hstco hmods₁ at hmodt₁
        apply Nat.chineseRemainder_modEq_unique hstco hmods₂ at hmodt₂
        have : s₁ ≡ s₂ [MOD (s * t)] := by
          exact ModEq.trans hmodt₁ (id (ModEq.symm hmodt₂))
        rw [<-hst] at this
        have : s₁ % (n + 1) = s₂ % (n + 1) := by exact this
        have h1 : s₁ % (n + 1) = s₁ := by apply Nat.mod_eq_of_lt; exact Nat.lt_add_one_iff.mpr hle₁
        have h2 : s₂ % (n + 1) = s₂ := by apply Nat.mod_eq_of_lt; exact Nat.lt_add_one_iff.mpr hle₂
        rw [h1, h2] at this
        exact SetCoe.ext this
      · intro ⟨d, hd⟩
        simp at hd
        obtain ⟨hneq1, ⟨hneqn, ⟨hdvd, hco⟩⟩⟩ := hd
        have heq : n + 1 = d * ((n + 1) / d) := by rw [Nat.mul_div_cancel_left' hdvd]
        have h1 : d > 1 := by
          by_contra hle
          push_neg at hle
          rcases lt_or_eq_of_le hle with h | h
          · simp at h
            simp [h] at hdvd
          · contradiction
        have h2 : (n + 1) / d > 1 := by
          by_contra hle
          push_neg at hle
          rcases lt_or_eq_of_le hle with h | h
          · replace h : (n + 1) / d = 0 := by exact lt_one_iff.mp h
            simp [h] at hco
            linarith
          · simp [h] at heq
            simp [heq] at hneq1
        obtain ⟨s, ⟨hs1, ⟨hs2, ⟨hmul, ⟨hgt, hlt⟩⟩⟩⟩⟩ := chinese_remainder d ((n + 1) / d) h1 h2 hco
        have : s ∈ {s | 1 < s ∧ s ≤ n ∧ n + 1 ∣ s * (s - 1)} := by
          simp
          split_ands
          · exact hgt
          · rw [<-heq] at hlt
            exact le_of_lt_succ hlt
          · rw [<-heq] at hmul
            exact hmul
        use ⟨s, this⟩
        simp [g]
        apply Nat.dvd_antisymm
        · have : (n + 1).gcd s ∣ n + 1 := by exact Nat.gcd_dvd_left (n + 1) s
          nth_rw 2 [heq] at this
          apply Coprime.dvd_of_dvd_mul_right ?_ this
          apply Coprime.coprime_dvd_left (Nat.gcd_dvd_right (n + 1) s)
          have : (n + 1) / d ∣ s - 1 := by refine (modEq_iff_dvd' ?_).mp (id (ModEq.symm hs2)); exact one_le_of_lt hgt
          apply Coprime.coprime_dvd_right this
          refine (coprime_self_sub_right ?_).mpr ?_
          · exact one_le_of_lt hgt
          · exact Nat.gcd_one_right s
        · apply Nat.dvd_gcd_iff.mpr
          constructor
          · exact hdvd
          · exact dvd_of_mod_eq_zero hs1
    exact Equiv.ofBijective g hg

  -- therefore, {i | i < n - 1 ∧ ∃ k : ℕ, f (i + 1) - f i = 1 / k} ≃ ((Finset.filter (fun d => Coprime d ((n + 1) / d)) (n + 1).divisors).erase 1).erase (n + 1)
  have congr_trans : {i | i < n - 1 ∧ ∃ k : ℕ, f (i + 1) - f i = 1 / k} ≃ ((Finset.filter (fun d => Coprime d ((n + 1) / d)) (n + 1).divisors).erase 1).erase (n + 1) := by
    exact congr_solution_dvd.trans congr_dvd_divisor

  -- prove card is equal
  have hcard : Nat.card {i | i < n - 1 ∧ ∃ k : ℕ, f (i + 1) - f i = 1 / k}
      = Nat.card (((Finset.filter (fun d => Coprime d ((n + 1) / d)) (n + 1).divisors).erase 1).erase (n + 1)) := by
    exact card_congr congr_trans

  rw [Set.Nat.card_coe_set_eq, card_eq_finsetCard] at hcard

  have hfincard : (((Finset.filter (fun d => Coprime d ((n + 1) / d)) (n + 1).divisors).erase 1).erase (n + 1)).card + 1 =
      (((Finset.filter (fun d => Coprime d ((n + 1) / d)) (n + 1).divisors).erase 1)).card := by
    apply Finset.card_erase_add_one
    simp
    exact not_eq_zero_of_lt hn
  have hfincard' : ((Finset.filter (fun d => Coprime d ((n + 1) / d)) (n + 1).divisors).erase 1).card + 1 =
      ((Finset.filter (fun d => Coprime d ((n + 1) / d)) (n + 1).divisors)).card := by
    apply Finset.card_erase_add_one
    simp

  -- show that result is 2 ^ ω(n + 1) - 2
  have hfincard'' : (((Finset.filter (fun d => Coprime d ((n + 1) / d)) (n + 1).divisors).erase 1).erase (n + 1)).card + 2 =
      2 ^ (n + 1).primeFactors.card := by
    rw [show 2 = 1 + 1 by simp, <-Nat.add_assoc, hfincard, hfincard', card_of_coprime]
    simp

  -- therefore 2 ^ ω(n + 1) ≥ 1002
  have : 2 ^ (n + 1).primeFactors.card ≥ 10002 := by
    rw [<-hfincard'', <-hcard, show 10002 = 10000 + 2 by simp]
    rel [hcardge]

  -- 2 ^ ω(n + 1) > 2 ^ 13
  have : 2 ^ 13 < 2 ^ (n + 1).primeFactors.card := by
    calc
      2 ^ 13 < 10002 := by simp
      _ ≤ 2 ^ (n + 1).primeFactors.card := by rel [this]

  -- ω ( n+ 1) > 13 → ω ( n+ 1) ≥ 14
  have : (n + 1).primeFactors.card > 13 := by
    apply Nat.pow_lt_pow_iff_right ?_ |>.mp this
    trivial

  have : (n + 1).primeFactors.card ≥ 14 := by exact this

  have : 2 ^ (n + 1).primeFactors.card ≥ 2 ^ 14 := by
    apply Nat.pow_le_pow_iff_right ?_ |>.mpr this
    trivial

  rw [<-hfincard'', <-hcard] at this

  -- 2 ^ 14 - 2 ≥ 15000
  calc
    {i | i < n - 1 ∧ ∃ k : ℕ, f (i + 1) - f i = 1 / k}.ncard = {i | i < n - 1 ∧ ∃ k : ℕ, f (i + 1) - f i = 1 / ↑k}.ncard + 2 - 2 := by rw [Nat.add_sub_cancel]
    _ ≥ 2 ^ 14 - 2 := by rel [this]
    _ ≥ 10000 + 5000 := by simp
