import Mathlib

theorem number_theory_98394 (a : ℕ → ℚ)
    (h0 : a 0 = 2020 / 2021)
    (h : ∀ k, ∃ m n : ℕ, m > 0 ∧ n > 0 ∧ m.Coprime n ∧ a k = m / n ∧ a (k + 1) = (m + 18) / (n + 19)) :
    ∑ᶠ j ∈ {j | ∃ t : ℕ, 0 < t ∧ a j = t / (t + 1)}, (j + 1) = 59 := by
  have hd (n : ℕ) : a n > 0 := by
    induction' n with m hm
    . rw [h0]
      norm_num
    . specialize h m
      obtain ⟨p, q, hp, hq, hpq, hpqm, hpqm'⟩ := h
      rw [hpqm']
      positivity

  have ht (n : ℕ) : (∃ t : ℕ, 0 < t ∧ a n = t / (t + 1)) ↔ (a n).num + 1 = (a n).den := by
    constructor <;> rintro h'
    . obtain ⟨t, ht, hat⟩ := h'
      have ht₁ : (t / (t + 1) : ℚ).num = t := by
        have : (t / (t + 1) : ℚ) = (↑(t : ℤ) / ↑(↑(t + 1) : ℤ)) := by congr; norm_cast
        rw [this]
        apply Rat.num_div_eq_of_coprime
        . simp
        . simp
          norm_cast
          refine Nat.coprime_self_add_right.mpr (Nat.gcd_one_right _)
      have ht₂ : (t / (t + 1) : ℚ).den = t + 1 := by
        zify
        rw [show (t + 1 : ℤ) = ↑(t + 1) by norm_cast, show (t + 1 : ℚ) = ↑(↑(t + 1) : ℤ) by norm_cast]
        apply Rat.den_div_eq_of_coprime
        . simp
        . simp
          norm_cast
          refine Nat.coprime_self_add_right.mpr (Nat.gcd_one_right _)
      rw [hat, ht₁, ht₂]
      norm_cast
    . use (a n).num.toNat
      simp
      and_intros
      . exact hd n
      . have := Rat.num_nonneg.mpr (le_of_lt (hd n))
        rw [show ((a n).num.toNat : ℚ) = (a n).num by norm_cast; exact Int.toNat_of_nonneg this]
        rw_mod_cast [h']
        exact Eq.symm (Rat.divInt_self (a n))

  have hp (n : ℕ) : a (n + 1) = ((a n).num + 18) / ((a n).den + 19) := by
    obtain ⟨p, q, hp, hq, hpq, h, h'⟩ := h n
    rw [h']
    congr <;> (rw [h]; apply eq_comm.mp)
    . norm_cast
      apply Rat.num_div_eq_of_coprime
      . norm_cast
      . simpa
    . zify
      apply Rat.den_div_eq_of_coprime
      . norm_cast
      . simpa

  have h1 : a 1 = 1019/1020 := by rw [hp, h0]; norm_num
  have h2 : a 2 = 1037/1039 := by rw [hp, h1]; norm_num
  have h3 : a 3 = 1055/1058 := by rw [hp, h2]; norm_num
  have h4 : a 4 = 1073/1077 := by rw [hp, h3]; norm_num
  have h5 : a 5 = 1091/1096 := by rw [hp, h4]; norm_num
  have h6 : a 6 = 1109/1115 := by rw [hp, h5]; norm_num
  have h7 : a 7 = 161/162 := by rw [hp, h6]; norm_num
  have h8 : a 8 = 179/181 := by rw [hp, h7]; norm_num
  have h9 : a 9 = 197/200 := by rw [hp, h8]; norm_num
  have h10 : a 10 = 215/219 := by rw [hp, h9]; norm_num
  have h11 : a 11 = 233/238 := by rw [hp, h10]; norm_num
  have h12 : a 12 = 251/257 := by rw [hp, h11]; norm_num
  have h13 : a 13 = 269/276 := by rw [hp, h12]; norm_num
  have h14 : a 14 = 287/295 := by rw [hp, h13]; norm_num
  have h15 : a 15 = 305/314 := by rw [hp, h14]; norm_num
  have h16 : a 16 = 323/333 := by rw [hp, h15]; norm_num
  have h17 : a 17 = 31/32 := by rw [hp, h16]; norm_num
  have h18 : a 18 = 49/51 := by rw [hp, h17]; norm_num
  have h19 : a 19 = 67/70 := by rw [hp, h18]; norm_num
  have h20 : a 20 = 85/89 := by rw [hp, h19]; norm_num
  have h21 : a 21 = 103/108 := by rw [hp, h20]; norm_num
  have h22 : a 22 = 121/127 := by rw [hp, h21]; norm_num
  have h23 : a 23 = 139/146 := by rw [hp, h22]; norm_num
  have h24 : a 24 = 157/165 := by rw [hp, h23]; norm_num
  have h25 : a 25 = 175/184 := by rw [hp, h24]; norm_num
  have h26 : a 26 = 193/203 := by rw [hp, h25]; norm_num
  have h27 : a 27 = 211/222 := by rw [hp, h26]; norm_num
  have h28 : a 28 = 229/241 := by rw [hp, h27]; norm_num
  have h29 : a 29 = 19/20 := by rw [hp, h28]; norm_num

  have coprime_lemma (m : ℕ) : (19 + 18 * m).Coprime (20 + 19 * m) := by
    rw [show 19 + 18 * m = 18 * (m + 1) + 1 by ring, show 20 + 19 * m = 19 * (m + 1) + 1 by ring]
    apply Nat.coprime_mul_succ
    . norm_cast
    . simp

  have h_num (m : ℕ) : ((19 + 18 * m : ℚ) / (20 + 19 * m)).num = 19 + 18 * m := by
    rw [show (19 + 18 * m : ℚ) = ↑(19 + 18 * m : ℤ) by norm_cast, show (20 + 19 * m : ℚ) = ↑(20 + 19 * m : ℤ) by norm_cast]
    apply Rat.num_div_eq_of_coprime
    . linarith
    . norm_cast
      exact coprime_lemma m

  have h_den (m : ℕ) : ((19 + 18 * m : ℚ) / (20 + 19 * m)).den = 20 + 19 * m := by
    zify
    rw [show (19 + 18 * m : ℚ) = ↑(19 + 18 * m : ℤ) by norm_cast, show (20 + 19 * m : ℚ) = ↑(20 + 19 * m : ℤ) by norm_cast]
    apply Rat.den_div_eq_of_coprime
    . linarith
    . norm_cast
      exact coprime_lemma m

  have h30 (n : ℕ) : a (29 + n) = (19 + 18 * n) / (20 + 19 * n) := by
    induction' n with m hm
    . rw [h29]
      norm_num
    . rw [← add_assoc, hp]
      congr 1
      . rw [hm, h_num]
        norm_cast
      . rw [hm, h_den]
        norm_cast

  have hs : {j | ∃ t : ℕ, 0 < t ∧ a j = t / (t + 1)} = ({0, 1, 7, 17, 29} : Finset ℕ) := by
    ext n
    simp
    rw [ht]
    constructor <;> rintro h'
    . match n with
      | 0 => simp
      | 1 => simp
      | 2 => rw [h2] at h'; norm_num at h'
      | 3 => rw [h3] at h'; norm_num at h'
      | 4 => rw [h4] at h'; norm_num at h'
      | 5 => rw [h5] at h'; norm_num at h'
      | 6 => rw [h6] at h'; norm_num at h'
      | 7 => simp
      | 8 => rw [h8] at h'; norm_num at h'
      | 9 => rw [h9] at h'; norm_num at h'
      | 10 => rw [h10] at h'; norm_num at h'
      | 11 => rw [h11] at h'; norm_num at h'
      | 12 => rw [h12] at h'; norm_num at h'
      | 13 => rw [h13] at h'; norm_num at h'
      | 14 => rw [h14] at h'; norm_num at h'
      | 15 => rw [h15] at h'; norm_num at h'
      | 16 => rw [h16] at h'; norm_num at h'
      | 17 => simp
      | 18 => rw [h18] at h'; norm_num at h'
      | 19 => rw [h19] at h'; norm_num at h'
      | 20 => rw [h20] at h'; norm_num at h'
      | 21 => rw [h21] at h'; norm_num at h'
      | 22 => rw [h22] at h'; norm_num at h'
      | 23 => rw [h23] at h'; norm_num at h'
      | 24 => rw [h24] at h'; norm_num at h'
      | 25 => rw [h25] at h'; norm_num at h'
      | 26 => rw [h26] at h'; norm_num at h'
      | 27 => rw [h27] at h'; norm_num at h'
      | 28 => rw [h28] at h'; norm_num at h'
      | 29 => simp
      | m + 30 =>
        specialize h30 (m + 1)
        rw [show 29 + (m + 1) = m + 30 by ring] at h30
        rw [h30, h_num, h_den] at h'
        norm_cast at h'
        omega
    . obtain rfl | rfl | rfl | rfl | rfl := h'
      all_goals (simp [h0, h1, h7, h17, h29]; norm_num)
  rw [hs]
  rw [finsum_mem_eq_toFinset_sum]
  simp