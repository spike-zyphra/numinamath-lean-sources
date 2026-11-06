import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/-
  Show that there is precisely one sequence  $ a_1,a_2,...$  of integers which satisfies
  $ a_1\equal{}1, a_2>1,$  and  $ a_{n\plus{}1}^3\plus{}1\equal{}a_n a_{n\plus{}2}$  for  $ n \ge 1$ .
-/

theorem number_theory_8495 :
    ∃! a : ℕ → ℤ, a 0 = 1 ∧ a 1 > 1 ∧ ∀ n, (a (n + 1)) ^ 3 + 1 = a n * a (n + 2) := by

  let pred (a : ℕ → ℤ) := a 0 = 1 ∧ a 1 > 1 ∧ ∀ n, (a (n + 1)) ^ 3 + 1 = a n * a (n + 2)
  let pred'(a : ℕ → ℤ) (m : ℕ) := a 0 = 1 ∧ a 1 > 1 ∧ ∀ n ≤ m, (a (n + 1)) ^ 3 + 1 = a n * a (n + 2)

  -- pred a → pred' a m for any m
  have pred_to_pred' (a : ℕ → ℤ) (ha : pred a) (m : ℕ) : pred' a m := by
    obtain ⟨h1, ⟨h2, h3⟩⟩ := ha
    simp [pred', h1, h2]
    intro n hn
    exact h3 n

  -- pred a m → pred a n for any m ≥ n
  have pred_to_lower (a : ℕ → ℤ) (m n : ℕ) (ha : pred' a m) (hn : n ≤ m) : pred' a n := by
    obtain ⟨h1, ⟨h2, h3⟩⟩ := ha
    simp [pred', h1, h2]
    intro k hk
    exact h3 k (Nat.le_trans hk hn)

  -- prove a 1 = 2
  have a_2_eq_2 (a : ℕ → ℤ) (m : ℕ) (ha : pred' a m) (hm : m ≥ 1) : a 1 = 2 := by
    obtain ⟨h1, ⟨h2, h3⟩⟩ := ha
    have : m ≥ 0 := by exact Nat.zero_le m
    obtain ha3 := h3 0 this
    simp [h1] at ha3
    obtain ha4 := h3 1 hm
    simp at ha4
    rw [<-ha3] at ha4
    have : a 1 ∣ (a 1 ^ 3 + 1) ^ 3 + 1 := by use a 3
    have : 0 ≡ 2 [ZMOD (a 1)] := by
      calc
        0 ≡ (a 1 ^ 3 + 1) ^ 3 + 1 [ZMOD (a 1)] := by exact Dvd.dvd.zero_modEq_int this
        _ ≡ (0 ^ 3 + 1) ^ 3 + 1 [ZMOD (a 1)] := by
          apply Int.ModEq.add_right
          apply Int.ModEq.pow 3
          apply Int.ModEq.add_right
          apply Int.ModEq.pow 3
          apply Dvd.dvd.modEq_zero_int
          exact Int.dvd_refl (a 1)
        _ ≡ 2 [ZMOD (a 1)] := by exact rfl
    have hdvd : a 1 ∣ 2 := by exact Int.dvd_of_emod_eq_zero (id (Int.ModEq.symm this))
    have hle : a 1 ≤ 2 := by apply Int.le_of_dvd; trivial; exact hdvd
    exact Int.le_antisymm hle h2

  have a_pos (a : ℕ → ℤ) (m n : ℕ) (ha : pred' a m) (hn : n ≤ m + 2) (hm : m ≥ 1) : a n > 0 := by
    have ⟨ha1, ⟨_, ha3⟩⟩ := ha
    induction n using Nat.caseStrongInductionOn
    · simp [ha1]
    · rename_i n' ih
      by_cases hn' : n' = 0
      · simp [hn']
        simp [a_2_eq_2 a m ha hm]
      · have : n' ≥ 1 := by exact one_le_iff_ne_zero.mpr hn'
        have hn0 : n' - 1 ≤ m + 2 := by
          calc
            n' - 1 ≤ n' := by exact sub_le n' 1
            _ ≤ n' + 1 := by exact Nat.le_add_right n' 1
            _ ≤ m + 2 := by rel [hn]
        have heq : a (n' - 1) * a (n' - 1 + 2) = a (n' - 1 + 1) ^ 3 + 1:= by
          apply Eq.symm
          apply ha3 (n' - 1)
          calc
            n' - 1 = n' + 1 - 1 - 1 := by rw [Nat.add_sub_cancel]
            _ ≤ m + 2 - 1 - 1 := by rel [hn]
            _ = m := by simp
        have hn1 : n' - 1 + 2 = n' + 1 := by
          rw [show 2 = 1 + 1 by exact rfl, <-Nat.add_assoc, Nat.sub_add_cancel]
          exact this
        have hn2 : n' - 1 + 1 = n' := by
          rw [Nat.sub_add_cancel]
          exact this
        rw [hn1, hn2] at heq
        have hge1 : a (n' - 1) > 0 := by
          apply ih (n' - 1)
          · exact sub_le n' 1
          · exact hn0
        have hge2 : a n' ^ 3 + 1 > 0 := by
          have : n' ≤ m + 2 := by exact le_of_succ_le hn
          calc
            a n' ^ 3 + 1 > 0 ^ 3 + 1 := by rel [ih n' (refl n') this]
            _ = 1 := by simp
            _ > 0 := by trivial
        have : 0 ≤ a (n' - 1) := by exact Int.le_of_lt hge1
        apply Int.lt_of_mul_lt_mul_left ?_ this
        simp [heq]
        exact hge2

  -- prove a (n + 1) ∣ (a (n + 2)) ^ 3 + 1
  have dvd (a : ℕ → ℤ) (m n : ℕ) (ha : pred' a m) (hn : n ≤ m) (hm : m ≥ 1) : a (n + 1) ∣ (a (n + 2)) ^ 3 + 1 := by
    have ⟨_, ⟨_, ha3⟩⟩ := ha
    induction n using Nat.caseStrongInductionOn
    · have ha3' := ha3 1 hm
      simp [ha3']
    · rename_i n' _
      have hn' : n' ≤ m := by exact le_of_succ_le hn
      have ha3' := ha3 n' hn'
      have ha3'' := ha3 (n' + 1) hn
      rw [Nat.add_assoc, show (1 + 1 = 2) by rfl, Nat.add_assoc, show (1 + 2 = 3) by rfl] at ha3''
      have : IsCoprime (a (n' + 2)) (a (n' + 1)) := by
        refine Int.isCoprime_iff_gcd_eq_one.mpr ?_
        refine Tactic.NormNum.int_gcd_helper' (- a (n' + 2) ^ 2) (a (n' + 3)) ?h₁ ?h₂ ?h₃
        · use a (n' + 2); simp
        · use a (n' + 1); simp
        · rw [<-ha3'']; ring
      have : IsCoprime (a (n' + 2)) ((a (n' + 1)) ^ 3) := by
        exact IsCoprime.pow_right this
      have : (a (n' + 2)) * ((a (n' + 1)) ^ 3) ∣ (a (n' + 1) * a (n' + 3)) ^ 3 + (a (n' + 1)) ^ 3 := by
        refine IsCoprime.mul_dvd this ?H1 ?H2
        · rw [<-ha3'']
          have : (a (n' + 2) ^ 3 + 1) ^ 3 + a (n' + 1) ^ 3 ≡ 0 [ZMOD (a (n' + 2))] := by
            calc
              (a (n' + 2) ^ 3 + 1) ^ 3 + a (n' + 1) ^ 3 ≡ (0 ^ 3 + 1) ^ 3 + a (n' + 1) ^ 3 [ZMOD (a (n' + 2))] := by
                apply Int.ModEq.add_right (a (n' + 1) ^ 3)
                apply Int.ModEq.pow 3
                apply Int.ModEq.add_right 1
                apply Int.ModEq.pow 3
                apply Dvd.dvd.modEq_zero_int
                trivial
              _ ≡ 1 + a (n' + 1) ^ 3 [ZMOD (a (n' + 2))] := by simp
              _ ≡ 0 [ZMOD (a (n' + 2))] := by
                apply Int.ModEq.symm
                apply Dvd.dvd.zero_modEq_int
                use a n'
                rw [add_comm, ha3']
                ring
          exact Int.dvd_of_emod_eq_zero this
        · apply Int.dvd_add
          · use a (n' + 3) ^ 3
            ring
          · exact Int.dvd_refl (a (n' + 1) ^ 3)
      have hdvd : a (n' + 2) ∣ ((a (n' + 1) * a (n' + 3)) ^ 3 + (a (n' + 1)) ^ 3) / ((a (n' + 1)) ^ 3) := by
        apply Int.dvd_div_of_mul_dvd
        rw [mul_comm]
        exact this
      have : ((a (n' + 1) * a (n' + 3)) ^ 3 + (a (n' + 1)) ^ 3) / ((a (n' + 1)) ^ 3) = a (n' + 1 + 2) ^ 3 + 1 := by
        rw [Nat.add_assoc, show (1 + 2 = 3) by rfl]
        rw [Int.add_ediv_of_dvd_right]
        · have : a (n' + 1) > 0 := by
            apply a_pos a m (n' + 1) ha
            · exact le_add_right_of_le hn
            · exact hm
          have : a (n' + 1) ^ 3 ≠ 0 := by
            refine Ne.symm (Int.ne_of_lt ?_)
            exact Lean.Omega.Int.pos_pow_of_pos (a (n' + 1)) 3 this
          rw [mul_pow, Int.mul_ediv_cancel_left _ this, Int.ediv_self this]
        · exact Int.dvd_refl (a (n' + 1) ^ 3)
      rw [<-this]
      exact hdvd

  -- prove if pred' a m and pred' b m, than a n = b n for n≤ m+2
  have unique (a b : ℕ → ℤ) (m n : ℕ) (ha : pred' a m) (hb : pred' b m) (hm : m ≥ 1) (hn : n ≤ m + 2) : a n = b n := by
    have ⟨ha1, ⟨ha2, ha3⟩⟩ := ha
    have ⟨hb1, ⟨hb2, hb3⟩⟩ := hb
    induction n using Nat.caseStrongInductionOn
    · simp [ha1, hb1]
    · rename_i n' ih
      by_cases hn' : n' = 0
      · simp [hn']
        rw [a_2_eq_2 a m ha hm, a_2_eq_2 b m hb hm]
      · have : n' ≥ 1 := by exact one_le_iff_ne_zero.mpr hn'
        have hn0 : n' - 1 ≤ m + 2 := by
          calc
            n' - 1 ≤ n' := by exact sub_le n' 1
            _ ≤ n' + 1 := by exact Nat.le_add_right n' 1
            _ ≤ m + 2 := by rel [hn]
        have hn1 : n' - 1 ≤ m := by
          calc
            n' - 1 ≤ n' + 1 - 1 - 1 := by exact Nat.le_refl (n' - 1)
            _ ≤ m + 2 - 1 - 1 := by rel [hn]
            _ = m := by simp
        have heq : a (n' - 1) * a (n' - 1 + 2) = b (n' - 1) * b (n' - 1 + 2) := by
          rw [<-ha3 (n' - 1), <-hb3 (n' - 1)]
          congr
          apply ih (n' - 1 + 1)
          rw [Nat.sub_add_cancel]
          · exact this
          · calc
              n' - 1 + 1 = n' := by rw [Nat.sub_add_cancel this]
              _ ≤ n' + 1 := by exact Nat.le_add_right n' 1
              _ ≤ m + 2 := by rel [hn]
          · exact hn1
          · exact hn1
        have hn' : n' - 1 + 2 = n' + 1 := by
          rw [show 2 = 1 + 1 by exact rfl, <-Nat.add_assoc, Nat.sub_add_cancel this]
        rw [hn', ih (n' - 1)] at heq
        rw [Int.mul_eq_mul_left_iff] at heq
        · exact heq
        · apply Ne.symm (Int.ne_of_lt (a_pos b m (n' - 1) hb hn0 hm))
        · exact sub_le n' 1
        · exact hn0

  -- prove the existence of a such that pred' a m for any m
  have exists_a (m : ℕ) : ∃ a : ℕ → ℤ, pred' a m := by
    induction m using Nat.caseStrongInductionOn
    · let a₁ (n : ℕ) : ℤ :=
        match n with
        | 0 => 1
        | 1 => 2
        | 2 => 9
        | _ => 0
      use a₁
      simp [pred', a₁]
    · rename_i m' ih
      obtain ⟨a, ⟨ha1, ⟨ha2, ha3⟩⟩⟩ := ih m' (refl m')
      by_cases hm' : m' = 0
      · let a' (n : ℕ) : ℤ :=
          match n with
          | 0 => 1
          | 1 => 2
          | 2 => 9
          | 3 => 365
          | _ => 0
        use a'
        simp [pred', a', hm']
        intro n hn
        interval_cases n
        all_goals simp
      · have hm' : m' ≥ 1 := by exact one_le_iff_ne_zero.mpr hm'
        let a' (n : ℕ) : ℤ := if n = m' + 3 then ((a (m' + 2)) ^ 3 + 1) / a (m' + 1) else a n
        use a'
        simp [a']
        split_ands
        · simp
          exact ha1
        · simp
          exact ha2
        · intro n hn
          have hm : n ≠ m' + 3 := by by_contra heq; rw [heq] at hn; linarith
          simp [if_neg hm]
          have hm : n ≠ m' + 2 := by by_contra heq; rw [heq] at hn; linarith
          simp [if_neg hm]
          rcases lt_or_eq_of_le hn with hlt | heq
          · have hm : n ≠ m' + 1 := by by_contra heq; rw [heq] at hn; linarith
            simp [if_neg hm]
            apply ha3 n
            exact le_of_lt_succ hlt
          · simp [heq]
            have : a (m' + 1) ∣ (a (m' + 2) ^ 3 + 1)  := by
              apply dvd a m' m' ⟨ha1, ⟨ha2, ha3⟩⟩
              exact Nat.le_refl m'
              exact hm'
            nth_rw 1 [<-Int.mul_div_cancel' this]
            refine (Int.mul_eq_mul_left_iff ?h.refine_2.refine_2.inr.h).mpr ?h.refine_2.refine_2.inr.a
            · have : a (m' + 1) > 0 := by
                apply a_pos a m' (m' + 1) ⟨ha1, ⟨ha2, ha3⟩⟩
                exact le_succ (m' + 1)
                exact hm'
              exact Ne.symm (Int.ne_of_lt this)
            · exact Int.div_eq_ediv_of_dvd this

  -- prove the existence of a such that pred a
  have exists_a' : ∃ a : ℕ → ℤ, pred a := by
    let a (n : ℕ) : ℤ :=
      let a' := (exists_a (n + 1)).choose
      a' n
    use a
    split_ands
    · simp only [reduceAdd, a]
      exact (exists_a 1).choose_spec.left
    · simp [a, reduceAdd]
      exact (exists_a (1 + 1)).choose_spec.right.1
    · intro n
      simp [a]

      let a_n := (exists_a (n + 1)).choose
      have pred_a_n := (exists_a (n + 1)).choose_spec

      let a_n_1 := (exists_a (n + 1 + 1)).choose
      have pred_a_n_1 := (exists_a (n + 1 + 1)).choose_spec

      have heq1 : a_n_1 (n + 1) = a_n (n + 1) := by
        apply unique a_n_1 a_n (n + 1) (n + 1) (pred_to_lower a_n_1 (n + 2) (n + 1) pred_a_n_1 ?_) pred_a_n
        exact Nat.le_add_left 1 n
        exact Nat.le_add_right (n + 1) 2
        exact le_succ (n + 1)

      let a_n_2 := (exists_a (n + 2 + 1)).choose
      have pred_a_n_2 := (exists_a (n + 2 + 1)).choose_spec

      have heq2 : (exists_a (n + 2 + 1)).choose (n + 2) = a_n (n + 2) := by
        apply unique a_n_2 a_n (n + 1) (n + 2) (pred_to_lower a_n_2 (n + 2 + 1) (n + 1) pred_a_n_2 ?_) pred_a_n
        exact Nat.le_add_left 1 n
        exact le_succ (n + 2)
        refine Nat.add_le_add_right ?_ 1
        exact Nat.le_add_right n 2

      simp [a_n_1, a_n_2] at heq1 heq2
      rw [heq1, heq2]
      simp [a_n]
      obtain h := (exists_a (n + 1)).choose_spec.right.right
      apply h n
      exact Nat.le_add_right n 1

  -- use a to prove the theorem
  obtain ⟨a, ha⟩ := exists_a'
  use a
  constructor
  · exact ha
  · -- prove the uniqueness of a
    intro b hb
    apply funext
    intro n
    by_cases hn : n = 0
    · simp [hn, hb.left, ha.left]
    · have hn' : n ≥ 1 := by exact one_le_iff_ne_zero.mpr hn
      apply unique b a n n
      · exact pred_to_pred' b hb n
      · exact pred_to_pred' a ha n
      · exact hn'
      · exact Nat.le_add_right n 2
