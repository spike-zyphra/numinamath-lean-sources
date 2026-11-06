import Mathlib

open Finset

set_option maxHeartbeats 0

/- The partial sum of an arithmetic progression. -/
lemma sum_arith (a d : ℕ) : ∑ i : Fin n, (a + d * i) = n * (2 * a + d * (n - 1)) / 2 := by
  -- prove by induction on n
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have h1 : ∑ i : Fin (n + 1), (a + d * i) = (a + d * n) + ∑ i : Fin n, (a + d * i):= by
      rw [Fin.sum_univ_succAbove _ (Fin.last n)]
      simp
    rw [h1]
    rw [ih]
    by_cases hn : n = 0
    · simp [hn]
    · rw [add_comm, ←Nat.add_mul_div_right]
      apply Nat.cast_inj (R := ℤ) |>.mp
      simp
      rw [Nat.cast_sub (by exact Nat.one_le_iff_ne_zero.mpr hn)]
      ring_nf
      simp

/- Show that M 1 = {2 ^ k | k ∈ ℕ} -/
lemma M_one_eq_two_pow {M : ℕ → Set ℕ}
    (hM : ∀ d ≥ 1, M d = {x : ℕ | x > 0 ∧ ¬ ∃ n ≥ 2, ∃ a : Fin n → ℕ, (∀ i, a i > 0) ∧ (∀ i, (hi : i + 1 < n) → a ⟨i + 1, hi⟩ = a ⟨i, Nat.lt_of_succ_lt hi⟩ + d) ∧ x = ∑ i, a i}) :
    M 1 = {2 ^ k | k ∈ Set.univ} := by
  ext x
  -- Apply the lemma, we obtain that x ∉ M 1 ↔ x = 0 ∨ ∃ n a, n ≥ 2 ∧ x = n * (2 * a + n + 1) / 2
  have hnot_in_iff : x ∉ M 1 ↔ x = 0 ∨ ∃ n a, n ≥ 2 ∧ x = n * (2 * a + n + 1) / 2 := by
    constructor <;> intro h
    · -- If x ∉ M 1
      rw [hM] at h
      simp at h
      by_cases hx : x = 0
      · -- Case x = 0
        simp [hx]
      · -- Case x > 0
        have hx : 0 < x := by exact Nat.zero_lt_of_ne_zero hx
        simp [hx] at h
        obtain ⟨n, hn, a, ha, hdiff, hsum⟩ := h
        right
        use n, a ⟨0, by exact Nat.zero_lt_of_lt hn⟩ - 1, hn
        rw [hsum]
        have : ∀ i ∈ univ, a i = a ⟨0, by exact Nat.zero_lt_of_lt hn⟩ + 1 * i := by
          intro ⟨i, hi⟩ _
          induction i with
          | zero =>
            simp
          | succ i ih =>
            trans a ⟨i, by apply lt_trans ?_ hi; simp⟩ + 1
            · apply hdiff
            · rw [ih]
              simp
              ring
              simp
        rw [sum_congr rfl this]
        rw [sum_arith]
        apply Nat.cast_inj (R := ℤ) |>.mp
        simp
        rw [Nat.cast_sub, Nat.cast_sub]
        ring_nf
        apply ha
        exact Nat.one_le_of_lt hn
      · simp
    · -- If x = 0 or x = n * (2 * a + n + 1) / 2 for some n ≥ 2 and a
      rw [hM]
      simp
      rcases h with h | h
      · -- Case x = 0
        rw [h]
        simp
      · -- Case x = n * (2 * a + n + 1) / 2
        obtain ⟨n, a, hn, hx⟩ := h
        rw [hx]
        intro x
        use n, hn, fun i => a + 1 + i
        split_ands
        · simp
        · intro _ _
          simp
          ring
        · trans ∑ i : Fin n, (fun i ↦ a + 1 + 1 * ↑i) i
          · rw [sum_arith]
            apply Nat.cast_inj (R := ℤ) |>.mp
            push_cast
            rw [Nat.cast_sub]
            ring_nf
            exact Nat.one_le_of_lt hn
          · apply sum_congr rfl
            simp
      · simp
  -- Now we can prove the main result
  constructor <;> intro h
  · -- Assume x ∉ M 1。
    -- Then we have ¬ (x = 0 ∨ ∃ n a, n ≥ 2 ∧ x = n * (2 * a + n + 1) / 2)
    have h : ¬ (x = 0 ∨ ∃ n a, n ≥ 2 ∧ x = n * (2 * a + n + 1) / 2) := by
      exact (not_congr hnot_in_iff).mp fun a ↦ a h
    push_neg at h
    -- We claim that the prime factors of x can only be 2.
    have h_eq_empty : x.primeFactors.erase 2 = ∅ := by
      by_contra h_ne
      -- Otherwise, we can find a prime factor p of x that is not 2.
      let p := (x.primeFactors.erase 2).min' (nonempty_iff_ne_empty.mpr h_ne)
      have hp : p ∈ x.primeFactors.erase 2 := by
        exact min'_mem (x.primeFactors.erase 2) (nonempty_iff_ne_empty.mpr h_ne)
      simp at hp
      obtain ⟨hpne, hp, hdvd, hxne⟩ := hp
      -- Then p ≥ 3
      have hpge : p ≥ 2 := by
        exact Nat.Prime.two_le hp
      have hpge' : p ≥ 3 := by
        apply Nat.lt_of_le_of_ne hpge
        exact fun a ↦ hpne (id (Eq.symm a))
      have hxge : x ≥ p := by
        apply Nat.le_of_dvd ?_ hdvd
        apply Nat.pos_iff_ne_zero.mpr h.1
      by_cases hx : ¬ 2 ∣ x
      · -- If ¬ 2 ∣ x, then use n = 2 and a = (x - 3) / 2
        -- Then we have x ≠ 2 * (2 * a + 3) / 2 = x, which is a contradiction.
        obtain h := h.2 2 ((x - 3) / 2) (by simp)
        rw [Nat.mul_div_cancel', add_assoc, Nat.sub_add_cancel, Nat.mul_div_cancel_left] at h
        · simp at h
        · simp
        · apply le_trans hpge' hxge
        · suffices : Even (x - 3)
          · exact even_iff_two_dvd.mp this
          · refine Nat.Odd.sub_odd ?_ ?_
            · refine Nat.odd_iff.mpr ?_
              exact Nat.two_dvd_ne_zero.mp hx
            · exact Nat.odd_iff.mpr rfl
      -- Otherwise, x is an even number.
      simp at hx
      have h_two_dvd : 2 ∣ p + 1 := by
        suffices : Even (p + 1)
        · exact even_iff_two_dvd.mp this
        · refine Odd.add_one ?_
          exact Nat.Prime.odd_of_ne_two hp hpne
      by_cases hx' : x / p < (p + 1) / 2
      · -- If x / p < (p + 1) / 2, and 2x / p < 2
        have hle : 2 * x / p + 1 ≤ p := by
          rw [Nat.mul_div_assoc]
          apply Nat.le_div_iff_mul_le (by simp) |>.mp at hx'
          simp [mul_comm, mul_add] at hx'
          exact hx'
          exact hdvd
        by_cases hx'' : 2 * x / p < 2
        · -- Then 2 (x/p) = 1 or 2 (x/p) = 0.
          rw [Nat.mul_div_assoc _ hdvd] at hx''
          set t := 2 * (x / p) with ht
          interval_cases t
          · -- If x/p = 0, then x < p, which is a contradiction.
            simp at ht
            rcases ht with ht | ht
            · have : p ≠ 0 := by exact Nat.not_eq_zero_of_lt hpge
              contradiction
            · have : ¬ x < p := by
                simp
                exact hxge
              contradiction
          · -- If 2(x / p) = 1, then 2 ∣ 1, which is a contradiction.
            have : 2 ∣ 1 := by
              use x / p
            simp at this
        · -- If 2 * (x / p) ≥ 2, then we can use n = (2x/p) and a = p - (2 * x / p + 1)) / 2
          obtain h := h.2 (2 * x / p) ((p - (2 * x / p + 1)) / 2) (by exact Nat.le_of_not_lt hx'')
          -- Then x ≠ (2 * x / p) * (2 * a + 2 * (p - (2 * x / p + 1)) / 2 + 1) / 2 = x which is a contradiction.
          rw [Nat.mul_div_cancel', add_assoc, Nat.sub_add_cancel, Nat.div_mul_cancel, Nat.mul_div_cancel_left] at h
          · simp at h
          · simp
          · exact Dvd.dvd.mul_left hdvd 2
          · exact hle
          · suffices : Even (p - (2 * x / p + 1))
            · exact even_iff_two_dvd.mp this
            · apply Nat.Odd.sub_odd
              · exact Nat.Prime.odd_of_ne_two hp hpne
              · refine Even.add_one ?_
                apply even_iff_two_dvd.mpr
                use x / p
                rw [Nat.mul_div_assoc _ hdvd]
      · -- If x / p ≥ (p + 1) / 2, then we can use n = p and a = (x / p - (p + 1) / 2) since x / p - (p + 1) / 2 ≥ 0.
        -- Then x ≠ p * (2 * a + 2 * (x / p - (p + 1) / 2)) / 2 = x, which is a contradiction.
        obtain h := h.2 p (x / p - (p + 1) / 2) hpge
        rw [Nat.mul_sub, Nat.mul_div_cancel', Nat.add_assoc, Nat.sub_add_cancel] at h
        · ring_nf at h
          rw [Nat.mul_div_cancel' hdvd, Nat.mul_div_cancel] at h
          · simp at h
          · simp
        · trans 2 * ((p + 1) / 2)
          · apply le_of_eq
            rw [Nat.mul_div_cancel']
            exact h_two_dvd
          · apply mul_le_mul
            · simp
            · exact Nat.le_of_not_lt hx'
            · simp
            · simp
        · exact h_two_dvd
    -- Therefore, the prime factors of x can only be 2.
    have : Nat.primeFactors x ⊆ {2} := by
      intro p h
      simp
      by_contra hp
      have : p ∈ x.primeFactors.erase 2 := by
        simp only [mem_erase]
        exact ⟨hp, h⟩
      simp [h_eq_empty] at this
    simp [h.1] at this
    rcases this with hx | hx
    · -- If x has no prime factors, then x = 1 = 2 ^ 0.
      use 0
      simp [hx]
    · -- Otherwise, x = 2 ^ k for some k.
      have : IsPrimePow x := by
        refine isPrimePow_iff_card_primeFactors_eq_one.mpr ?_
        simp [hx]
      obtain ⟨p, k, hp, hx'⟩ := this
      use k
      simp [←hx'.2, eq_comm]
      congr
      have : p ∈ x.primeFactors := by
        simp [h.1]
        split_ands
        · exact Prime.nat_prime hp
        · rw [←hx'.2]
          refine dvd_pow_self p ?_
          apply ne_of_gt hx'.1
      simp [hx] at this
      exact this
  · -- If x = 2 ^ k for some k.
    by_contra h'
    -- Prove by contradiction.
    -- Assume that x ∉ M 1.
    apply hnot_in_iff.mp at h'
    -- Then x = 0 or x = n * (2 * a + n + 1) / 2 for some n ≥ 2 and a.
    rcases h' with h' | h'
    · -- Cases x = 0
      simp [h'] at h
    · -- Case x = n * (2 * a + n + 1) / 2 for some n ≥ 2 and a.
      obtain ⟨n, a, hn, hx⟩ := h'
      simp [hx] at h
      obtain ⟨k, hk⟩ := h
      by_cases hn : 2 ∣ n
      · -- If n = 2 * m, then 2 ^ k = m * (2a + 2m + 1).
        obtain ⟨m, hm⟩ := hn
        simp [hm] at hk
        rw [mul_assoc, Nat.mul_div_cancel_left] at hk
        · -- Therefore 2 ∣ 2a+ 2m + 1, which is a contradiction.
          have : 2 * a + 2 * m + 1 ∣ 2 ^ k := by
            use m
            rw [hk, mul_comm]
          apply Nat.dvd_prime_pow (by norm_num) |>.mp at this
          obtain ⟨k', hk', heq⟩ := this
          by_cases hk' : k' = 0
          · simp [hk'] at heq
            simp [heq.2] at hm
            simp [hm] at hn
          · have : 2 ∣ 2 * a + 2 * m + 1 := by
              rw [heq]
              exact dvd_pow_self 2 hk'
            apply Nat.dvd_add_iff_right (by use a + m; ring) |>.mpr at this
            simp at this
        · simp
      · -- If n is odd, then 2 ∣ 2 * a + n + 1.
        have : Even (2 * a + n + 1) := by
          refine Odd.add_one ?_
          apply Even.add_odd
          use a
          ring
          refine Nat.odd_iff.mpr ?_
          exact Nat.two_dvd_ne_zero.mp hn
        have : 2 ∣ 2 * a + n + 1 := by
          exact even_iff_two_dvd.mp this
        rw [Nat.mul_div_assoc _ this] at hk
        -- Therefore, n ∣ 2 ^ k
        have : n ∣ 2 ^ k := by
          use (2 * a + n + 1) / 2
        apply Nat.dvd_prime_pow (by norm_num) |>.mp at this
        obtain ⟨k', hk', heq⟩ := this
        -- Therefore, 2 ∣ n, which is a contradiction.
        have : 2 ∣ n := by
          rw [heq]
          apply dvd_pow_self 2
          by_contra h
          simp [h] at heq
          rename_i hnge _
          simp [heq] at hnge
        contradiction

/- Show that M 2 = {n | n is a prime or 1}. -/
lemma M_two_eq_primes {M : ℕ → Set ℕ}
    (hM : ∀ d ≥ 1, M d = {x : ℕ | x > 0 ∧ ¬ ∃ n ≥ 2, ∃ a : Fin n → ℕ, (∀ i, a i > 0) ∧ (∀ i, (hi : i + 1 < n) → a ⟨i + 1, hi⟩ = a ⟨i, Nat.lt_of_succ_lt hi⟩ + d) ∧ x = ∑ i, a i}) :
    M 2 = {n | Nat.Prime n} ∪ {1} := by
  ext x
  -- Prove that x ∉ M 2 ↔ x = 0 ∨ ∃ n a, n ≥ 2 ∧ x = n * (2 * a + 2 * n) / 2
  have hnot_in_iff : x ∉ M 2 ↔ x = 0 ∨ ∃ n a, n ≥ 2 ∧ x = n * (2 * a + 2 * n) / 2 := by
    constructor <;> intro h
    · -- Apply the lemma sum_arith.
      rw [hM] at h
      simp at h
      by_cases hx : x = 0
      · simp [hx]
      · have hx : 0 < x := by exact Nat.zero_lt_of_ne_zero hx
        simp [hx] at h
        obtain ⟨n, hn, a, ha, hdiff, hsum⟩ := h
        right
        use n, a ⟨0, by exact Nat.zero_lt_of_lt hn⟩ - 1, hn
        rw [hsum]
        have : ∀ i ∈ univ, a i = a ⟨0, by exact Nat.zero_lt_of_lt hn⟩ + 2 * i := by
          intro ⟨i, hi⟩ _
          induction i with
          | zero =>
            simp
          | succ i ih =>
            trans a ⟨i, by apply lt_trans ?_ hi; simp⟩ + 2
            · apply hdiff
            · rw [ih]
              simp
              ring
              simp
        rw [sum_congr rfl this]
        rw [sum_arith]
        apply Nat.cast_inj (R := ℤ) |>.mp
        simp
        rw [Nat.cast_sub, Nat.cast_sub]
        simp
        ring_nf
        apply ha
        exact Nat.one_le_of_lt hn
      · simp
    · -- Apply the lemma sum_arith.
      rw [hM]
      simp
      rcases h with h | h
      · rw [h]
        simp
      · obtain ⟨n, a, hn, hx⟩ := h
        rw [hx]
        intro x
        use n, hn, fun i => a + 1 + 2 * i
        split_ands
        · simp
        · intro _ _
          simp
          ring
        · trans ∑ i : Fin n, (fun i ↦ a + 1 + 2 * ↑i) i
          · rw [sum_arith]
            apply Nat.cast_inj (R := ℤ) |>.mp
            push_cast
            rw [Nat.cast_sub]
            ring_nf
            exact Nat.one_le_of_lt hn
          · apply sum_congr rfl
            simp
      · simp
  constructor <;> intro h
  · -- Assume x ∉ M 2.
    -- THen we have ¬ (x = 0 ∨ ∃ n a, n ≥ 2 ∧ x = n * (2 * a + 2 * n) / 2)
    have h : ¬ (x = 0 ∨ ∃ n a, n ≥ 2 ∧ x = n * (2 * a + 2 * n) / 2) := by
      exact (not_congr hnot_in_iff).mp fun a ↦ a h
    push_neg at h
    simp
    by_cases h_eq_empty : x.primeFactors = ∅
    · -- If x.primeFactors = ∅, then x = 1.
      simp at h_eq_empty
      simp [h.1] at h_eq_empty
      simp [h_eq_empty]
    · -- Otherwise, we can find the minimum prime factor p of x.
      let p := x.primeFactors.min' (nonempty_iff_ne_empty.mpr h_eq_empty)
      have hp : p ∈ x.primeFactors := by
        exact min'_mem x.primeFactors (nonempty_iff_ne_empty.mpr h_eq_empty)
      simp at hp
      -- Therefore, x = p * t for some t
      obtain ⟨hp, ⟨t, ht⟩, hxne⟩ := hp
      by_cases hx : t ≥ p
      · -- If t ≥ p, then we can use n = p and a = t - p.
        -- x ≠ p * (p + t - p) = x, which is a contradiction.
        obtain h := h.2 p (t - p) (by exact Nat.Prime.two_le hp)
        rw [Nat.mul_div_assoc, ←mul_add, Nat.mul_div_cancel_left, Nat.sub_add_cancel hx, ht] at h
        · simp at h
        · simp
        · rw [←mul_add]
          simp
      · -- If t < p, then t has no prime factors since p is the minimum prime factor of x.
        simp at hx
        have : t.primeFactors = ∅ := by
          by_contra h_ne
          obtain ⟨q, hq⟩ : t.primeFactors.Nonempty := by
            exact nonempty_iff_ne_empty.mpr h_ne
          simp at hq
          have h₀ : q ≤ t := by
            apply Nat.le_of_dvd ?_ hq.2.1
            by_contra h
            simp at h
            simp [h] at hq
          have h₁ : p ≤ q := by
            apply min'_le
            simp [hq, h.1]
            apply Nat.dvd_trans hq.2.1
            exact Dvd.intro_left p (id (Eq.symm ht))
          have : ¬ p > t := by
            simp
            exact Nat.le_trans h₁ h₀
          contradiction
        -- Therefore, t = 1 or 0.
        -- If t = 0, then x = 0, which is a contradiction.
        simp at this
        -- If t = 1, then x = p, which is a prime number.
        rcases this with ht' | ht'
        · simp [ht'] at ht
          simp [ht] at h
        · simp [ht'] at ht
          simp [ht, hp]
  · -- Assume x = p for some prime p.
    simp at h
    by_contra h'
    -- By contradiction, assume that x ∉ M 2.
    -- Therefore, x = 0 or x = n * (2 * a + 2 * n) / 2 for some n ≥ 2 and a.
    apply hnot_in_iff.mp at h'
    rcases h with h | h
    · -- Case x = 1
      simp [h] at h'
      obtain ⟨n, hn, x, hx⟩ := h'
      rw [Nat.mul_div_assoc] at hx
      · have : n ∣ 1 := by
          simp [hx]
        have : n ≤ 1 := by
          apply Nat.le_of_dvd (by norm_num) this
        linarith
      · rw [←mul_add]
        simp
    · -- Case x is a prime p.
      rcases h' with h' | h'
      · simp [h'] at h
        norm_num at h
      · obtain ⟨n, a, hn, hx⟩ := h'
        rw [Nat.mul_div_assoc] at hx
        -- Then n ∣ x, which implies n = x or n = 1.
        -- Since n ≥ 2, we have n = x
        have : n ∣ x := by
          simp [hx]
        have : n = x := by
          exact (Nat.dvd_prime_two_le h hn).mp this
        simp [this] at hx hn
        -- Therefore, a + x = 1.
        -- However, x = n ≥ 2, which is a contradiction.
        have : (2 * a + 2 * x) / 2 = 1 := by
          by_contra hne
          rcases lt_or_gt_of_ne hne with h | h
          · have : x < x := by
              nth_rw 1 [hx]
              nth_rw 3 [show x = x * 1 by simp]
              gcongr
            simp at this
          · have : x > x := by
              nth_rw 1 [hx]
              nth_rw 3 [show x = x * 1 by simp]
              gcongr
            simp at this
        rw [←mul_add, Nat.mul_div_cancel_left] at this
        · have : 1 ≥ 2 := by
            rw [←this]
            exact le_add_of_le_right hn
          simp at this
        · simp
        · rw [←mul_add]
          simp

/- Show that if x ∈ M3, then x = 2 ^ k * p for some primes p ≠ 2 or p = 1. -/
lemma M_three_eq_pow_mul_prime {M : ℕ → Set ℕ}
    (hM : ∀ d ≥ 1, M d = {x : ℕ | x > 0 ∧ ¬ ∃ n ≥ 2, ∃ a : Fin n → ℕ, (∀ i, a i > 0) ∧ (∀ i, (hi : i + 1 < n) → a ⟨i + 1, hi⟩ = a ⟨i, Nat.lt_of_succ_lt hi⟩ + d) ∧ x = ∑ i, a i})
    (hx : x ∈ M 3) :
  ∃ p k, (p = 1 ∨ Nat.Prime p) ∧ p ≠ 2 ∧ x = 2 ^ k * p := by
  -- Prove that x ∉ M 3 ↔ x = 0 ∨ ∃ n a, n ≥ 2 ∧ x = n * (2 * a + 3 * n - 1) / 2
  have hnot_in_iff : x ∉ M 3 ↔ x = 0 ∨ ∃ n a, n ≥ 2 ∧ x = n * (2 * a + 3 * n - 1) / 2 := by
    -- Apply the lemma sum_arith and simplify.
    constructor <;> intro h
    · rw [hM] at h
      simp at h
      by_cases hx : x = 0
      · simp [hx]
      · have hx : 0 < x := by exact Nat.zero_lt_of_ne_zero hx
        simp [hx] at h
        obtain ⟨n, hn, a, ha, hdiff, hsum⟩ := h
        right
        use n, a ⟨0, by exact Nat.zero_lt_of_lt hn⟩ - 1, hn
        rw [hsum]
        have : ∀ i ∈ univ, a i = a ⟨0, by exact Nat.zero_lt_of_lt hn⟩ + 3 * i := by
          intro ⟨i, hi⟩ _
          induction i with
          | zero =>
            simp
          | succ i ih =>
            trans a ⟨i, by apply lt_trans ?_ hi; simp⟩ + 3
            · apply hdiff
            · rw [ih]
              simp
              ring
              simp
        rw [sum_congr rfl this]
        rw [sum_arith]
        apply Nat.cast_inj (R := ℤ) |>.mp
        simp
        rw [Nat.cast_sub, Nat.cast_sub]
        simp
        rw [Nat.cast_sub]
        ring_nf
        apply ha
        · trans 0 + 3 * 2
          · simp
          · gcongr
            simp
        exact Nat.one_le_of_lt hn
      · simp
    · rw [hM]
      simp
      rcases h with h | h
      · rw [h]
        simp
      · obtain ⟨n, a, hn, hx⟩ := h
        rw [hx]
        intro x
        use n, hn, fun i => a + 1 + 3 * i
        split_ands
        · simp
        · intro _ _
          simp
          ring
        · trans ∑ i : Fin n, (fun i ↦ a + 1 + 3 * ↑i) i
          · rw [sum_arith]
            apply Nat.cast_inj (R := ℤ) |>.mp
            push_cast
            rw [Nat.cast_sub, Nat.cast_sub]
            simp
            ring_nf
            exact Nat.one_le_of_lt hn
            trans 0 + 3 * 2
            · simp
            · gcongr
              simp
          · apply sum_congr rfl
            simp
      · simp
  -- Since x ∈ M 2, we have ¬ (x = 0 ∨ ∃ n a, n ≥ 2 ∧ x = n * (2 * a + 3 * n - 1) / 2)
  have h : ¬ (x = 0 ∨ ∃ n a, n ≥ 2 ∧ x = n * (2 * a + 3 * n - 1) / 2) := by
    exact (not_congr hnot_in_iff).mp fun a ↦ a hx
  push_neg at h
  -- Assume that x = 2 ^ k * t for some k and odd t.
  let k := x.factorization 2
  have ⟨t, ht⟩ : 2 ^ k ∣ x := by
    exact Nat.ordProj_dvd x 2
  have hndvd : ¬ 2 ^ (k + 1) ∣ x := by
    refine Nat.pow_succ_factorization_not_dvd ?_ ?_
    · simp [h.1]
    · norm_num
  have hndvd : ¬ 2 ∣ t := by
    rw [ht] at hndvd
    simp [pow_add] at hndvd
    by_contra h
    have : 2 ^ k * 2 ∣ 2 ^ k * t := by
      exact Nat.mul_dvd_mul_left (2 ^ k) h
    contradiction
  by_cases ht_factor : t.primeFactors.Nonempty
  · -- If t has a prime factor p, then  p ≥ 3
    obtain ⟨p, hp⟩ := ht_factor
    have hp_prime : Nat.Prime p := by
      exact Nat.prime_of_mem_primeFactors hp
    have hp_ne_2 : p ≠ 2 := by
      intro h
      have : 2 ∣ t := by
        rw [←h]
        exact Nat.dvd_of_mem_primeFactors hp
      contradiction
    have hp_gt : 2 < p := by
      apply lt_of_le_of_ne ?_ (Ne.symm hp_ne_2)
      exact Nat.Prime.two_le hp_prime
    -- Assume that t = p * q for some q.
    have ⟨q, hq⟩ : p ∣ t := by
      exact Nat.dvd_of_mem_primeFactors hp
    by_cases hq_le : q ≤ 2
    · -- If q ≤ 2, then q = 0 or 1 or 2.
      -- Since ¬ 2 ∣ t, we have q = 1.
      interval_cases q
      · simp at hq
        simp [hq] at hndvd
      · -- So t = p and x = 2 ^ k * p.
        simp at hq
        simp [hq] at ht
        simp [ht]
        right
        use p
        split_ands
        · exact Nat.prime_of_mem_primeFactors hp
        · by_contra hp
          simp [hp] at hq
          simp [hq] at hndvd
        · use k
      · simp [hq] at hndvd
    · -- If q ≥ 3.
      simp at hq_le
      by_cases hk : k = 0
      · -- If k = 0, then x = p * q.
        simp [ht, hk] at h
        -- We can use n = 2 and a = (t - 5) / 2 since t = p * q ≥ 3 * 3 = 9.
        -- Therefore x ≠ 2 * (2 * a + 3) / 2 = x, which is a contradiction.
        obtain h := h.2 2 ((t - 5) / 2) (by simp)
        rw [Nat.mul_div_cancel'] at h
        · norm_num at h
          rw [Nat.sub_add_cancel] at h
          · simp at h
          · rw [hq]
            trans 3 * 3
            · simp
            · gcongr
              · exact hp_gt
              · exact hq_le
        · suffices : Even (t - 5)
          · exact even_iff_two_dvd.mp this
          · refine Nat.Odd.sub_odd ?_ ?_
            · refine Nat.odd_iff.mpr ?_
              exact Nat.two_dvd_ne_zero.mp hndvd
            · exact Nat.odd_iff.mpr rfl
      · -- Otherwise, let r := min p q.
        let r := min p q
        have hr : r ≥ 2 := by
          apply le_min
          · exact Nat.Prime.two_le hp_prime
          · exact Nat.le_of_succ_le hq_le
        -- Then we can use n = r and a = (x / r - (3 * r - 1) / 2).
        -- Then x ≠ r * (2 * a + 3 * r - 1) / 2 = x, which is a contradiction.
        obtain h := h.2 r (x / r - (3 * r - 1) / 2) hr
        rw [Nat.mul_sub 2, Nat.mul_div_cancel', Nat.add_sub_assoc, Nat.sub_add_cancel, Nat.mul_div_assoc, Nat.mul_div_cancel_left, Nat.mul_div_cancel'] at h
        · simp at h
        · simp [r, ht, hq]
          by_cases hp : p ≤ q
          · simp [hp]
            apply Dvd.dvd.mul_left
            simp
          · simp at hp
            simp [le_of_lt hp]
            apply Dvd.dvd.mul_left
            simp
        · simp
        · simp
        · -- we need to show that 3 r - 1 ≤ 2 (x / r)
          simp [ht, hq]
          -- 3r - 1 ≤ 4 r ≤ 4 (t / r) ≤ 2 (2 ^ k * t / 4) = 2 (x / r)
          trans 2 * (2  * (p * q) / r) + 1
          · trans 4 * r
            · gcongr
              simp
            · trans 4 * r + 1
              · simp
              · rw [Nat.mul_div_assoc]
                ring_nf
                gcongr
                apply Nat.le_div_iff_mul_le ?_ |>.mpr
                · gcongr
                  · exact Nat.min_le_left p q
                  · exact Nat.min_le_right p q
                · simp [r]
                  constructor
                  · exact Nat.zero_lt_of_lt hp_gt
                  · exact Nat.zero_lt_of_lt hq_le
                · simp [r]
                  by_cases hp : p ≤ q
                  · simp [hp]
                  · simp at hp
                    simp [le_of_lt hp]
          · gcongr
            exact Nat.le_self_pow hk 2
        · trans 3 * 2
          · simp
          · gcongr
        · suffices : Even (3 * r - 1)
          · apply even_iff_two_dvd.mp this
          · refine Nat.Odd.sub_odd ?_ ?_
            · refine Nat.odd_mul.mpr ?_
              constructor
              · exact Nat.odd_iff.mpr rfl
              · simp [r]
                by_cases hp : p ≤ q
                · simp [hp]
                  exact Nat.Prime.odd_of_ne_two hp_prime hp_ne_2
                · simp at hp
                  simp [le_of_lt hp]
                  by_contra h
                  simp at h
                  have : 2 ∣ q := by
                    exact even_iff_two_dvd.mp h
                  have : 2 ∣ t := by
                    rw [hq]
                    exact Dvd.dvd.mul_left this p
                  contradiction
            · exact Nat.odd_iff.mpr rfl
  · -- If t has no prime factors, then t = 1 or 0.
    -- Both cases are trivial.
    simp at ht_factor
    interval_cases t
    · simp at hndvd
    · simp [ht]

/-
  5. (GDR 2) For every integer $d \geq 1$, let $M_{d}$ be the set of all positive integers that cannot be written as a sum of an arithmetic
  progression with difference $d$, having at least two terms and consisting of positive integers. Let $A=M_{1}, B=M_{2} \backslash\{2\}, C=M_{3}$.
  Prove that every $c \in C$ may be written in a unique way as $c=a b$ with $a \in A, b \in B$.
-/
theorem number_theory_23688 {M : ℕ → Set ℕ}
    (hM : ∀ d ≥ 1, M d = {x : ℕ | x > 0 ∧ ¬ ∃ n ≥ 2, ∃ a : Fin n → ℕ, (∀ i, a i > 0) ∧ (∀ i, (hi : i + 1 < n) → a ⟨i + 1, hi⟩ = a ⟨i, Nat.lt_of_succ_lt hi⟩ + d) ∧ x = ∑ i, a i})
    (hA : A = M 1) (hB : B = M 2 \ {2}) (hC : C = M 3) :
    ∀ c ∈ C, ∃! a ∈ A, ∃! b ∈ B, c = a * b := by
  -- Note that A = {2 ^ k | k ≥ 0}, B = {p | p ≠ 2 is a prime or p = 1}, C = {2 ^ k * p | p ≠ 2 is a prime or p = 1}.
  rw [hA, hB, hC]
  rw [M_one_eq_two_pow hM, M_two_eq_primes hM]
  simp
  intro c hc
  apply M_three_eq_pow_mul_prime hM at hc
  -- Since c ∈ C, we have c = 2 ^ k * p for some k and p.
  obtain ⟨p, k, hp, hpne, hc⟩ := hc
  -- let a = 2 ^ k ∈ M 1 and b = p ∈ M 2.
  use 2 ^ k
  simp
  constructor
  · -- The existences follows.
    use p
    simp [hc, hpne, hp]
    split_ands
    · tauto
    · intro _ _
      tauto
  · -- Then we prove the uniqueness.
    -- Assume that there exists another pair (2 ^ a, b) such that c = 2 ^ a * b
    intro a ha
    obtain ⟨b, ⟨⟨hb₁, hb₂⟩, hceq⟩, hunique⟩ := ha
    simp at hunique
    rw [hc] at hceq
    -- We have 2 ^ k * p = 2 ^ a * b.
    -- Since p and b are odds, we have 2  ^ k ∣ 2 ^ a and 2 ^ a ∣ 2 ^ k
    have h₁ : 2 ^ k ∣ 2 ^ a := by
      suffices : 2 ^ k ∣ 2 ^ a * b
      · apply Nat.Coprime.dvd_mul_right ?_ |>.mp this
        refine Nat.Coprime.pow_left k ?_
        refine Nat.coprime_two_left.mpr ?_
        rcases hb₁ with h | h
        · simp [h]
        · exact Nat.Prime.odd_of_ne_two h hb₂
      · rw [←hceq]
        simp
    have h₂ : 2 ^ a ∣ 2 ^ k := by
      suffices : 2 ^ a ∣ 2 ^ k * p
      · apply Nat.Coprime.dvd_mul_right ?_ |>.mp this
        refine Nat.Coprime.pow_left a ?_
        refine Nat.coprime_two_left.mpr ?_
        rcases hp with h | h
        · simp [h]
        · exact Nat.Prime.odd_of_ne_two h hpne
      · rw [hceq]
        simp
    -- Therefore, we have 2 ^ a = 2 ^ k, which implies a = k.
    have : 2 ^ a = 2 ^ k := by
      exact Nat.dvd_antisymm h₂ h₁
    simp at this
    exact this
