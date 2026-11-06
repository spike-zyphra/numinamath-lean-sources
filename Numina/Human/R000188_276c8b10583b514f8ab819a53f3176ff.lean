import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat
/-
  For any positive integer  $n$ , let  $D_n$  denote the greatest common divisor
  of all numbers of the form  $a^n + (a + 1)^n + (a + 2)^n$  where  $a$  varies among all positive integers.
  (a) Prove that for each  $n$ ,  $D_n$  is of the form  $3^k$  for some integer  $k \ge 0$ .
  (b) Prove that, for all  $k\ge 0$ , there exists an integer  $n$  such that  $D_n = 3^k$ .
-/
theorem number_theory_8513_1 (D : ℕ → ℕ)
    (hdvd : ∀ n ≥ 1, ∀ a ≥ 1, D n ∣ a ^ n + (a + 1) ^ n + (a + 2) ^ n)
    (_ : ∀ n ≥ 1, ∀ d', (∀ a ≥ 1, d' ∣ a ^ n + (a + 1) ^ n + (a + 2) ^ n) → d' ∣ D n)
    (n : ℕ) (hn : n ≥ 1):
    ∃ k ≥ 0, D n = 3 ^ k := by

  -- prove any p ∣ D n →  p = 3
  have hfactor_eq_3 (p : ℕ) (hp : Nat.Prime p) (hpdvd : p ∣ D n) : p = 3 := by
    -- show D n ∣ (p + 3) ^ n - p ^ n
    have hdvd₁ : D n ∣ p ^ n + (p + 1) ^ n + (p + 2) ^ n := by
      apply hdvd n hn p
      exact Prime.one_le hp
    have hdvd₂ : D n ∣ (p + 1) ^ n + (p + 2) ^ n + (p + 3) ^ n := by
      apply hdvd n hn (p + 1)
      exact Nat.le_add_left 1 p
    have hdvd₃ : D n ∣ ((p + 1) ^ n + (p + 2) ^ n + (p + 3) ^ n) - (p ^ n + (p + 1) ^ n + (p + 2) ^ n) := by
      exact dvd_sub' hdvd₂ hdvd₁
    rw [Nat.sub_add_eq, Nat.add_comm] at hdvd₃
    nth_rw 3 [Nat.add_comm] at hdvd₃
    rw [<-Nat.add_assoc, Nat.add_sub_add_right, <-Nat.sub_add_eq, Nat.add_sub_add_right] at hdvd₃
    have hdvd₄ : p ∣ (p + 3) ^ n - p ^ n := by
      exact Nat.dvd_trans hpdvd hdvd₃
    -- therefore, p ∣ (p + 3) ^ n → p ∣ 3 ^ n
    have hdvd₅ : p ∣ (p + 3) ^ n := by
      have : (p + 3) ^ n = (p + 3) ^ n - p ^ n + p ^ n := by
        rw [Nat.sub_add_cancel]
        refine pow_le_pow_of_le_left ?h n
        exact Nat.le_add_right p 3
      rw [this]
      refine (Nat.dvd_add_iff_right hdvd₄).mp ?_
      refine dvd_pow_self p ?hn
      exact not_eq_zero_of_lt hn
    have hdvd₆ : p ∣ p + 3 := by exact Nat.Prime.dvd_of_dvd_pow hp hdvd₅
    -- p = 3
    have : p ∣ 3 := by exact Nat.dvd_add_self_left.mp hdvd₆
    apply Nat.prime_dvd_prime_iff_eq hp ?_ |>.mp this
    norm_num
  -- therefore prime factors of D n is {3} or ∅
  have hfactors : (D n).primeFactors ⊆ {3} := by
    intro p hp
    simp at hp
    simp
    exact hfactor_eq_3 p hp.left hp.right.left

  -- use k = (D n).factorization 3
  use (D n).factorization 3
  constructor
  · exact Nat.zero_le ((D n).factorization 3)
  · -- show 3 ^ k = D n
    refine eq_pow_of_factorization_eq_single ?h.right.hn ?h.right.h
    · by_contra heq
      obtain h := hdvd n hn 1 (Nat.le_refl 1)
      simp [heq] at h
    · exact Finsupp.support_subset_singleton.mp hfactors

theorem number_theory_8513_2 (D : ℕ → ℕ)
    (hdvd : ∀ n ≥ 1, ∀ a ≥ 1, D n ∣ a ^ n + (a + 1) ^ n + (a + 2) ^ n)
    (hgreatest : ∀ n ≥ 1, ∀ d', (∀ a ≥ 1, d' ∣ a ^ n + (a + 1) ^ n + (a + 2) ^ n) → d' ∣ D n) (k : ℕ) :
    ∃ n, D n = 3 ^ k := by
  by_cases hk : k = 0
  · -- k = 0, use 2
    use 2
    simp [hk]
    -- D 2 = 3 ^ k'
    obtain ⟨k', ⟨_, hk'2⟩⟩ := number_theory_8513_1 D hdvd hgreatest 2 (show 2 ≥ 1 by simp)
    have hdvd₁ := hdvd 2 (show 2 ≥ 1 by simp) 1 (show 1 ≥ 1 by simp)
    norm_num at hdvd₁
    rw [hk'2] at hdvd₁
    rw [show 14 = 2 * 7 by simp] at hdvd₁
    -- 3 ^ k' ∣ 2 * 7 → k' = 0
    by_cases hk' : k' = 0
    · simp [hk'] at hk'2
      exact hk'2
    · have : Nat.Coprime (3 ^ k') 2 := by
        apply Coprime.pow_left k'
        norm_num
      have : 3 ^ k' ∣ 7 := by exact Coprime.dvd_of_dvd_mul_left this hdvd₁
      have : 3 ∣ 7 := by
        refine dvd_of_pow_dvd ?hk this
        exact one_le_iff_ne_zero.mpr hk'
      norm_num at this
  · have hk : k ≥ 1 := by exact one_le_iff_ne_zero.mpr hk
    -- use 3 ^ (k - 1)
    let n := 3 ^ (k - 1)
    use n
    -- some facts
    have hodd3 : Odd 3 := by exact odd_iff.mpr rfl
    have hoddn : Odd n := by exact Odd.pow hodd3
    have hpvn : padicValNat 3 n = k - 1 := by exact padicValNat.prime_pow (k - 1)
    -- compute ν₃(0 ^ n + 1 ^ n + 2 ^ n) 
    have pv0 : padicValNat 3 (0 ^ n + 1 ^ n + 2 ^ n) = k := by
      have : 0 ^ n = 0 := by
        refine Nat.zero_pow ?_
        exact Fin.size_pos'
      simp only [this]
      have : padicValNat 3 (1 ^ n + 2 ^ n) = padicValNat 3 (1 + 2) + padicValNat 3 n := by
        refine padicValNat.pow_add_pow hodd3 ?_ ?_ hoddn
        · exact dvd_of_mod_eq_zero rfl
        · exact of_decide_eq_false rfl
      rw [zero_add, this, hpvn]
      simp
      rw [Nat.add_sub_cancel' hk]
    -- prove ν₃(a ^ n + (a + 1) ^ n + (a + 2) ^ n) ≥ k
    have pva (a : ℕ) : padicValNat 3 (a ^ n + (a + 1) ^ n + (a + 2) ^ n) ≥ k := by
      induction a with
      | zero =>
        exact Nat.le_of_eq (id (Eq.symm pv0))
      | succ b ih =>
        have : (b + 1) ^ n + (b + 1 + 1) ^ n + (b + 1 + 2) ^ n = b ^ n + (b + 1) ^ n + (b + 2) ^ n + ((b + 3) ^ n - b ^ n) := by
          nth_rw 8 [add_comm]
          rw [<-Nat.add_assoc, <-Nat.add_assoc, Nat.sub_add_cancel]
          · ring
          · apply Nat.pow_le_pow_of_le_left
            simp
        have h1 : padicValRat 3 (b ^ n + (b + 1) ^ n + (b + 2) ^ n) ≥ k := by norm_cast
        have h2 (h : ¬ 3 ∣ b) : padicValNat 3 ((b + 3) ^ n - b ^ n) = k := by
          calc
            padicValNat 3 ((b + 3) ^ n - b ^ n) = padicValNat 3 ((b + 3) - b) + padicValNat 3 n := by
              apply padicValNat.pow_sub_pow hodd3
              · norm_num
              · simp
              · simp
                exact h
              · exact Ne.symm (NeZero.ne' n)
            _ = 1 + (padicValNat 3 n) := by simp
            _ = 1 + (k - 1) := by rw [hpvn]
            _ = k := by rw [Nat.add_sub_cancel' hk]
        have h3 (h : 3 ∣ b) : padicValNat 3 ((b + 3) ^ n - b ^ n) ≥ n := by
          refine (padicValNat_dvd_iff_le ?ha).mp ?_
          · have : (b + 3) ^ n > b ^ n := by
              apply pow_lt_pow_left
              · simp
              · exact Nat.zero_le b
              · exact Ne.symm (NeZero.ne' n)
            exact Nat.sub_ne_zero_iff_lt.mpr this
          · refine dvd_sub' ?h₁ ?h₂
            · refine (Nat.pow_dvd_pow_iff ?_).mpr ?_
              · exact Ne.symm (NeZero.ne' n)
              · simp; exact h
            · apply (Nat.pow_dvd_pow_iff ?_).mpr h
              exact Ne.symm (NeZero.ne' n)
        have h4 : padicValNat 3 ((b + 3) ^ n - b ^ n) ≥ k := by
          by_cases h : 3 ∣ b
          · apply Nat.le_trans ?_ (h3 h)
            simp [n]
            have (k : ℕ) : k + 1 ≤ 3 ^ k := by
              induction k with
              | zero => simp
              | succ k' ih =>
                calc
                  k' + 1 + 1 ≤ 3 ^ k' + 3 ^ k' := by rel [ih, show 1 ≤ 3 ^ k' by exact one_le_pow' k' 2]
                  _ = 2 * 3 ^ k' := by ring
                  _ ≤ 3 * 3 ^ k' := by rel [show 2 ≤ 3 by simp]
                  _ = 3 ^ (k' + 1) := by rw [<-Nat.pow_add_one']
            obtain h := this (k - 1)
            rw [Nat.sub_add_cancel hk] at h
            exact h
          · simp [h2 h]
        have : padicValRat 3 (((b + 1) ^ n + (b + 1 + 1) ^ n + (b + 1 + 2) ^ n) : ℕ) ≥ k := by
          rw [this]
          have : (((b ^ n + (b + 1) ^ n + (b + 2) ^ n) : ℕ) + (((b + 3) ^ n - b ^ n) : ℕ) : ℚ) ≠ (0 : ℚ) := by
            norm_cast
            rw [<-this]
            apply Nat.ne_of_gt
            suffices : (b + 1 + 2) ^ n > 0
            · exact Nat.add_pos_right ((b + 1) ^ n + (b + 1 + 1) ^ n) this
            · exact pos_of_neZero ((b + 1 + 2) ^ n)
          apply @padicValRat.min_le_padicValRat_add 3 at this
          simp at this
          rcases this with hl | hr
          · apply le_trans h1 at hl
            simp [hl]
          · norm_cast at hr
            apply le_trans h4 at hr
            norm_cast
        norm_cast at this
    -- prove padicValNat 3 (1 + 2 ^ n + 3 ^ n) = k if k ≥ 2
    have pv1 (hk : k ≥ 2) : padicValNat 3 (1 + 2 ^ n + 3 ^ n) = k := by
      have : padicValRat 3 (1 + 2 ^ n + 3 ^ n : ℕ) = padicValRat 3 (1 + 2 ^ n : ℕ) := by
        rw [Nat.cast_add]
        apply padicValRat.add_eq_of_lt
        · norm_cast
          rw [Nat.add_assoc]
          apply Nat.ne_of_gt
          exact Fin.size_pos'
        · norm_cast
          apply Nat.ne_of_gt
          exact Fin.size_pos'
        · norm_cast
          exact NeZero.ne (3 ^ n)
        · norm_cast
          have : 0 ^ n = 0 := by
            refine Nat.zero_pow ?_
            exact Fin.size_pos'
          simp [this] at pv0
          simp [pv0]
          have (k : ℕ) (hk : k ≥ 2) : k < 3 ^ (k - 1) := by
            induction k with
            | zero => linarith
            | succ k' ih =>
              match k' with
              | 0 => simp at hk
              | 1 => simp
              | k'' + 2 =>
                simp at ih ⊢
                calc
                  k'' + 2 + 1 < 3 ^ (k'' + 1) + 1 := by rel [ih]
                  _ < 3 ^ (k'' + 1) + 3 ^ (k'' + 1) := by rel [show 1 < 3 ^ (k'' + 1) by exact Nat.one_lt_pow' k'' 1]
                  _ = 2 * 3 ^ (k'' + 1) := by ring
                  _ ≤ 3 * 3 ^ (k'' + 1) := by rel [show 2 ≤ 3 by simp]
                  _ = 3 ^ (k'' + 2) := by rw [<-Nat.pow_add_one']
          exact this k hk
      norm_cast at this
      rw [this]
      have : 0 ^ n = 0 := by
        refine Nat.zero_pow ?_
        exact Fin.size_pos'
      simp [this] at pv0
      exact pv0

    apply Nat.dvd_antisymm
    · -- prove D n ∣ 3 ^ k, since D n = 3 ^ k' for some k', we prove k' ≤ k
      have hn : n ≥ 1 := by exact one_le_pow' (k - 1) 2
      obtain ⟨k', ⟨_, hk'2⟩⟩ := number_theory_8513_1 D hdvd hgreatest n hn
      simp [hk'2]
      refine Nat.pow_dvd_pow 3 ?_
      -- by contradiction,  assume k' > k
      by_contra hgt
      push_neg at hgt
      -- k' ≥ k + 1
      have hge : k' ≥ k + 1 := by exact hgt
      have hdvd' : 3 ^ (k + 1) ∣ 3 ^ k' := by exact pow_dvd_pow_iff_le_right'.mpr hgt
      obtain hdvd := hdvd n hn 1 (Nat.le_refl 1)
      rw [hk'2] at hdvd
      -- 3 ^ (k + 1) ∣ 1 ^ n + (1 + 1) ^ n + (1 + 2) ^ n
      have : 3 ^ (k + 1) ∣ 1 ^ n + (1 + 1) ^ n + (1 + 2) ^ n := by
        exact pow_dvd_of_le_of_pow_dvd hgt hdvd
      simp at this
      -- however, ¬ 3 ^ (k + 1) ∣ 1 ^ n + (1 + 1) ^ n + (1 + 2) ^ n
      have hndvd : ¬ 3 ^ (k + 1) ∣ 1 + 2 ^ n + 3 ^ n := by
        by_cases hk' : k ≥ 2
        · rw [<-pv1 hk']
          refine pow_succ_padicValNat_not_dvd ?_
          apply Nat.ne_of_gt
          rw [Nat.add_assoc]
          exact Fin.size_pos'
        · simp [n]
          interval_cases k
          norm_num
      contradiction
    · -- since 3 ^ k ∣ a ^ n + (a + 1) ^ n + (a + 2) ^ n for all a, 3 ^ k ∣ D n
      apply hgreatest n
      · exact one_le_pow' (k - 1) 2
      · intro a _
        obtain hdvd := @pow_padicValNat_dvd 3 ((a ^ n + (a + 1) ^ n + (a + 2) ^ n))
        exact pow_dvd_of_le_of_pow_dvd (pva a) hdvd
