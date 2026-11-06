import Mathlib


/- If p - 1 ∣ n + 1 , then either p ∣ a n ∨ p ∣ a (n + 1) -/
lemma cases_of_p_sub_one_dvd_n (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (h2 : ∀ n ≥ 1, a (n + 1) = (a n) ^ (n + 1) - 1) (hp : Nat.Prime p) (hodd : Odd p)
    (hn : p - 1 ∣ n + 1) : p ∣ a n ∨ p ∣ a (n + 1) := by
  by_cases hdvd : p ∣ a n
  · simp [hdvd]
  · -- Assume ¬ p ∣ a n.
    -- Since p - 1 ∣ n + 1, we have n ≥ 1.
    have : n ≥ 1 := by
      by_contra h
      simp at h
      simp [h] at hn
      have : p % 2 = 1 := by exact Nat.odd_iff.mp hodd
      simp [hn] at this
    -- Therefore, a (n + 1) = (a n) ^ (n + 1) - 1.
    right; rw [h2 n this]
    refine (Nat.modEq_iff_dvd' ?_).mp ?_
    · exact Nat.one_le_pow (n + 1) (a n) (ha n)
    · -- Assume that n + 1 = m (p - 1)
      -- Then a (n + 1) = (a n) ^ m ^ (p - 1) - 1 ≡ 1 - 1 = 0 [mod p].
      obtain ⟨m, hm⟩ := hn
      rw [hm, mul_comm, pow_mul]
      apply ZMod.natCast_eq_natCast_iff _ _ _ |>.mp
      simp; symm
      have : Fact (Nat.Prime p) := { out := hp }
      apply ZMod.pow_card_sub_one_eq_one
      by_contra h
      have : p ∣ (a n) ^ m := by
        apply Nat.modEq_zero_iff_dvd.mp
        apply ZMod.natCast_eq_natCast_iff _ _ _ |>.mp
        simp [h]
      apply Nat.Prime.dvd_of_dvd_pow hp at this
      contradiction

/- If n  is odd and p ∣ a (n + 1), then p ^ (n + 2) ∣ a (n + 3). -/
lemma dvd_of_odd_n (a : ℕ → ℕ) (ha : ∀ n, 0 < a n) (hp : Nat.Prime p)
    (h2 : ∀ n ≥ 1, a (n + 1) = (a n) ^ (n + 1) - 1) (hdvd : p ∣ a (n + 1)) (heven : Odd n) : p ^ (n + 2) ∣ a (n + 3) := by
  -- Since p ∣ a (n + 1), we only need to show that (a (n + 1)) ^ (n + 2) divides a (n + 3).
  trans a (n + 1) ^ (n + 2)
  · exact pow_dvd_pow_of_dvd hdvd (n + 2)
  · -- a (n + 3) = (a (n + 1) ^ (n + 2) - 1) ^ (n + 3) - 1 ≡ (-1) ^ (n + 3) - 1 = 0 [mod a (n + 1) ^ (n + 2)].
    -- Therefore, (a (n + 1)) ^ (n + 2) ∣ a (n + 3).
    have : a (n + 3) = (a (n + 1) ^ (n + 2) - 1) ^ (n + 3) - 1 := by
      rw [←h2, ←h2]
      all_goals simp
    rw [this]
    apply Int.natCast_dvd_natCast.mp
    apply Int.modEq_zero_iff_dvd.mp
    rw [Nat.cast_sub]; simp; rw [Nat.cast_sub]
    · trans (0 - 1) ^ (n + 3) - 1
      · gcongr
        refine Dvd.dvd.modEq_zero_int ?_; simp
      · simp; congr
        apply sub_eq_zero.mpr
        apply Even.neg_one_pow
        refine Nat.even_add'.mpr ?_
        simp [heven]
        exact Nat.odd_iff.mpr rfl
    · apply Nat.one_le_pow
      apply ha
    · apply Nat.one_le_pow
      simp
      by_contra h
      simp at h
      have : a (n + 1) = 1 := by
        apply le_antisymm h
        exact ha (n + 1)
      simp [this] at hdvd
      simp [hdvd] at hp
      norm_num at hp

/- If p ^ (k - 1) ∣ n + 1 and p ∣ a (n + 1) ∧ p - 1 ∣ n + 2, then p ^ k ∣ a (n + 1). -/
lemma dvd_of_dvd (a : ℕ → ℕ) (ha : 1 < a n) (hp : Nat.Prime p) (hn : n ≥ 1) (hk : k ≥ 1) (hdvd₁ : p ^ (k - 1) ∣ n + 1) (hodd : Odd p)
    (h2 : ∀ n ≥ 1, a (n + 1) = (a n) ^ (n + 1) - 1) (hdvd₂ : p ∣ a (n + 1)) (hdvd₀ : p - 1 ∣ n + 2) : p ^ k ∣ a (n + 1) := by
  have : Fact (Nat.Prime p) := {out := hp}
  rw [h2 n hn] at hdvd₂ ⊢
  -- Note that ¬ p ∣ a n since p ∣ a (n + 1) = (a n) ^ (n + 1) - 1.
  have hndvd :  ¬p ∣ a n := by
    by_contra h
    have : p ≤ 1 := by
      apply Nat.le_of_dvd (by simp)
      trans a n ^ (n + 1) - (a n ^ (n + 1) - 1)
      · apply Nat.dvd_sub' ?_ hdvd₂
        refine Dvd.dvd.pow h ?_; simp
      · rw [Nat.sub_sub_self]
        apply Nat.one_le_pow
        exact Nat.zero_lt_of_lt ha
    have : ¬ p ≤ 1 := by simp; exact Nat.Prime.one_lt hp
    contradiction
  -- We show that a n ^ (n + 1) ≡ (a n)⁻¹ [mod p].
  have hinv : a n ^ (n + 1) = 1 / (a n : ZMod p) := by
    -- In fact, it suffices to show that p ∣ a n ^ (n + 1)
    apply eq_div_iff ?_ |>.mpr
    · trans (a n) ^ (n + 2)
      · ring
      · -- Assume that n + 2 = m(p - 1).
        -- Then a n ^ (n + 1) = (a n) ^ m(p - 1) ≡ 1 [mod p].
        obtain ⟨m, hm⟩ := hdvd₀
        rw [hm, mul_comm, pow_mul]
        apply ZMod.pow_card_sub_one_eq_one
        intro h
        have : p ∣ (a n) ^ m := by
          apply (ZMod.natCast_zmod_eq_zero_iff_dvd _ p).mp
          simp [h]
        apply Nat.Prime.dvd_of_dvd_pow hp at this
        contradiction
    · intro h
      apply (ZMod.natCast_zmod_eq_zero_iff_dvd (a n) p).mp at h
      contradiction
  -- Therefore, p ∣ a n - 1.
  have hdvd₃ : p ∣ a n - 1 := by
    -- This is because p ∣ a (n + 1) = (a n) ^ (n + 1) - 1.
    -- So (a n)⁻¹ ≡ 1 [mod p] implies that a n ≡ 1 [mod p].
    apply Int.natCast_dvd_natCast.mp
    simp [Nat.cast_sub (le_of_lt ha)]
    apply Int.modEq_zero_iff_dvd.mp
    apply ZMod.intCast_eq_intCast_iff _ _ _ |>.mp
    suffices :  a n ^ (n + 1) - (1 : ZMod p) = 0
    · apply sub_eq_zero.mp at this
      simp [hinv] at this
      simp [this]
    · apply (ZMod.natCast_zmod_eq_zero_iff_dvd _ p).mpr at hdvd₂
      rw [Nat.cast_sub] at hdvd₂
      simpa using hdvd₂
      apply Nat.one_le_pow
      exact Nat.zero_lt_of_lt ha
  -- By lifting the exponent of p, we can show that ν(a n ^ (n + 1) - 1 ^ (n + 1)) = ν(a n - 1) + ν(n + 1) ≥ 1 + (k - 1) = k.
  have : padicValNat p (a n ^ (n + 1) - 1 ^ (n + 1)) ≥ k := by
    rw [padicValNat.pow_sub_pow hodd ha hdvd₃ hndvd (by simp)]
    trans 1 + (k - 1)
    · gcongr
      · refine one_le_padicValNat_of_dvd ?_ hdvd₃
        simp
        exact ha
      · apply padicValNat_dvd_iff_le ?_ |>.mp hdvd₁
        simp
    · rw [Nat.add_sub_cancel' hk]
  -- Therefore, p ^ k ∣ a n ^ (n + 1) - 1 ^ (n + 1) = a (n + 1).
  simp at this
  apply padicValNat_dvd_iff_le ?_ |>.mpr this
  apply ne_of_gt
  simp
  exact ha

/- Prove by induction that ∀ n ≥ 1, 1 < a n. -/
lemma one_lt_a (a : ℕ → ℕ) (h1 : a 1 = 2) (h2 : ∀ n ≥ 1, a (n + 1) = (a n) ^ (n + 1) - 1) : ∀ n ≥ 1, 1 < a n := by
  intro n hn
  induction n, hn using Nat.le_induction
  · simp [h1]
  · rename_i n hn ih
    rw [h2]
    apply lt_of_lt_of_le (b := 2 ^ (n + 1) - 1)
    · apply Nat.lt_sub_of_add_lt
      simp [pow_add]
      exact Nat.not_eq_zero_of_lt hn
    · gcongr; exact ih
    · exact hn

/- A sequence $a_{1}, a_{2}, \ldots$ of positive integers is defined recursively by $a_{1}=2$ and  $$ a_{n+1}=a_{n}^{n+1}-1 \quad \text { for } n \geq 1 $$  Prove that for every odd prime $p$ and integer $k$, some term of the sequence is divisible by $p^{k}$. -/
theorem number_theory_605875 (a : ℕ → ℕ) (ha : ∀ n, 0 < a n) (h1 : a 1 = 2) (h2 : ∀ n ≥ 1, a (n + 1) = (a n) ^ (n + 1) - 1) :
    ∀ p k, Odd p → Nat.Prime p → ∃ n ≥ 1, p ^ k ∣ a n := by
  intro p k hodd hp
  have hp_ge : p ≥ 2 := by exact Nat.Prime.two_le hp
  by_cases hk : k = 0
  · -- If k = 0, then p ^ k = 1, which divides every term of the sequence.
    use 1; simp [hk]
  · -- Assume k ≥ 1. Let n = p ^ (k - 1) * (p - 2).
    have hk : k ≥ 1 := by exact Nat.one_le_iff_ne_zero.mpr hk
    let n := p ^ (k - 1) * (p - 2)
    -- Note that p - 1 ∣ n + 1
    have hn : p - 1 ∣ n + 1 := by
      simp [n]
      apply Int.natCast_dvd_natCast.mp
      simp [Nat.cast_sub (Nat.one_le_of_lt hp_ge), Nat.cast_sub hp_ge]
      have : ↑p ^ (k - 1) * (↑p - 2) + 1 = p ^ (k - 1) * (p - 1) - (p ^ (k - 1) - 1 : ℤ) := by ring
      simp [this]
      apply Int.dvd_sub
      · simp
      · exact sub_one_dvd_pow_sub_one (p : ℤ) (k - 1)
    -- Since p - 1 ∣ n + 1, we can apply the lemma to obtain that either p ∣ a n or p ∣ a (n + 1).
    rcases cases_of_p_sub_one_dvd_n a ha h2 hp hodd hn with hdvd | hdvd
    · -- If p ∣ a n, let n' = n - 1.
      let n' := n - 1
      -- We can show that n' ≥ 1.
      have hn' : n' ≥ 1 := by
        simp [n', n]
        apply Nat.le_sub_of_add_le
        simp [n] at hdvd
        by_cases hp : p ≥ 4
        · trans 4 ^ (k - 1) * (4 - 2)
          · simp; apply Nat.one_le_pow; simp
          · gcongr
        · simp at hp
          interval_cases p
          · have : ¬ Odd 2 := by simp
            contradiction
          · simp
            by_cases hk : k ≥ 2
            · trans 3 ^ 1
              · simp
              · gcongr
                · simp
                · apply Nat.le_sub_of_add_le hk
            · simp at hk
              interval_cases k
              simp [n, h1] at hdvd
              apply Nat.le_of_dvd (by simp) at hdvd
              simp at hdvd
      have heq : n' + 1 = n := by
        rw [Nat.sub_add_cancel]
        apply le_trans hn'
        simp [n']
      rw [←heq] at hn hdvd
      -- Then applying the lemma dvd_of_dvd, we can show that p ^ (k + 1) ∣ a (n' + 1) = a n.
      use n' + 1; simp
      apply dvd_of_dvd a (one_lt_a a h1 h2 _ hn') hp hn' hk ?_ hodd h2 hdvd hn
      rw [heq]
      simp [n]
    · -- Otherwise, we have p ∣ a (n + 1).
      -- Note that n is an odd number.
      have hnodd : Odd n := by
        simp [n]
        apply Odd.mul
        · exact Odd.pow hodd
        · refine (Nat.odd_sub hp_ge).mpr ?_
          simp [hodd]
      -- By the lemma dvd_of_odd_n, we can show that p ^ (n + 2) ∣ a (n + 3).
      apply dvd_of_odd_n a ha hp h2 hdvd at hnodd
      use n + 3; simp
      -- Now it suffices to show that k ≤ n + 2 = p ^ (k - 1) * (p - 2) + 2.
      apply dvd_trans ?_ hnodd
      refine (Nat.pow_dvd_pow_iff_le_right hp_ge).mpr ?_
      simp [n]
      apply le_add_of_le_left
      clear * - hp hodd
      -- We are done by indction on k.
      induction k with
      | zero => simp
      | succ k ih =>
        have hp_ge : 1 ≤ p - 2 := by
          apply Nat.le_sub_of_add_le
          by_contra hp
          simp at hp
          have : p = 2 := by apply le_antisymm (Nat.le_of_lt_succ hp) <| Nat.Prime.two_le (by assumption)
          have : ¬ Odd p := by simp [this]
          contradiction
        by_cases hk : k ≥ 1
        · rw [Nat.sub_add_comm hk, Nat.pow_add_one]
          trans p ^ (k - 1) * (p - 2 + 1)
          · rw [mul_add, mul_one]
            gcongr
            apply Nat.one_le_pow
            exact Nat.Prime.pos hp
          · simp [mul_assoc]
            gcongr
            trans p * 1
            · apply Nat.cast_le (α := ℤ) |>.mp
              simp [Nat.cast_sub (Nat.Prime.two_le hp)]
              apply sub_nonneg.mp
              ring_nf; simp
            · gcongr
        · simp at hk
          simp [hk, hp_ge]
