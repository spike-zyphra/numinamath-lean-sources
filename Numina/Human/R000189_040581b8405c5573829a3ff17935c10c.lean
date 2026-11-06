import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/-
  A positive integer  $K$  is given. Define the sequence  $(a_n)$
  by  $a_1 = 1$  and  $a_n$  is the  $n$ -th positive integer greater than  $a_{n-1}$
  which is congruent to  $n$  modulo  $K$ .
  **(a)** Find an explicit formula for  $a_n$ .
  **(b)** What is the result if  $K = 2$ ?
-/
theorem number_theory_8517_1 (k : ℕ+) (a : ℕ+ → ℕ+) (ha₁ : a 1 = 1) (haₙ : ∀ n, a (n + 1) = (Nat.nth {m | m > a n ∧ m ≡ (n + 1) [MOD k]} n)) :
    ∀ n, (a n).val = n * (n - 1) * k / 2 + n := by

  -- abbreviate the predicate as p
  let p (n : ℕ+) (m : ℕ) := m > a n ∧ m ≡ (n + 1) [MOD k]

  -- show that the set of all elements satifying p is infinite
  have infinite (n : ℕ+) : (setOf (p n)).Infinite := by
    refine Set.infinite_of_forall_exists_gt ?h
    intro x
    use x + a n + 1 + (n + k - (x + a n) % k) % k
    constructor
    · simp [p]
      constructor
      · apply Nat.lt_add_right; rw [Nat.add_assoc]; apply Nat.lt_add_left; exact lt_add_one (a n).val
      · have h1 : (n + k - (x + a n) % k) % k ≡ n + k - (x + a n) % k [MOD k] := by exact mod_modEq _ _
        have h2 : x + a n ≡ (x + a n) % k [MOD k] := by exact ModEq.symm (mod_modEq (x + ↑(a n)) k)
        have h3 : x + a n + 1 ≡ (x + a n) % k + 1 [MOD k] := by exact ModEq.add_right 1 h2
        have h4 : (x + a n + 1) + (n + k - (x + a n) % k) % k ≡ ((x + a n) % k + 1) + (n + k - (x + a n) % k) [MOD k] := by exact ModEq.add h3 h1
        calc
          x + a n + 1 + (n + k - (x + a n) % k) % k = (x + a n + 1) + (n + k - (x + a n) % k) % k := by simp
          _ ≡ ((x + a n) % k + 1) + (n + k - (x + a n) % k) [MOD k] := by exact h4
          _ ≡  n + 1 [MOD k] := by
            rw [Nat.add_comm, <-Nat.add_assoc, Nat.sub_add_cancel]; ring_nf; exact add_modEq_right
            have : (x + ↑(a n)) % k < n + k := by refine Nat.lt_add_left ↑n ?h; refine mod_lt (x + ↑(a n)) ?h.a; exact PNat.pos k
            exact le_of_succ_le this
    · calc
        x < x + 1 := by exact lt_add_one x
        _ ≤ x + 1 + (↑(a n) + (↑n + ↑k - (x + ↑(a n)) % ↑k) % ↑k) := by apply Nat.le_add_right
        _ = x + ↑(a n) + 1 + (↑n + ↑k - (x + ↑(a n)) % ↑k) % ↑k := by ring

  -- prove a(n+1) satisfies the predicate
  have p_n (n : ℕ+) : p n (a (n + 1)) := by
    rw [haₙ]
    simp [p]
    exact Nat.nth_mem_of_infinite (infinite n) n

  -- prove a(n) + 1 + i * k satisy the predicate for all i
  have p_n_plus_1 (n : ℕ+) (i : ℕ) :
      p n (a n + 1 + i * k) := by
    constructor
    · refine Nat.lt_add_right (i * ↑k) ?left.h; exact lt_add_one (a n).val
    · by_cases hn : n = 1
      · simp [hn, ha₁]
        nth_rw 2 [<-Nat.add_zero 2]
        apply ModEq.add_left 2
        refine modEq_zero_iff_dvd.mpr ?_
        exact Nat.dvd_mul_left (↑k) i
      · have hn1 : n ≥ 1 := by exact PNat.one_le n
        have : n > 1 := by exact lt_of_le_of_ne hn1 fun a ↦ hn (id (Eq.symm a))
        have hmod := (p_n (n - 1)).right
        have h1 : (n - 1).val + 1 = n := by rw [PNat.sub_coe]; simp [if_pos this]; rw [Nat.sub_add_cancel]; exact hn1
        have : n - 1 + 1 = n := by exact Eq.symm (PNat.eq (id (Eq.symm h1)))
        rw [this, h1] at hmod
        calc
          ↑(a n) + 1 + i * ↑k ≡ n + 1 + i * k [MOD k] := by rel [hmod]
          _ ≡ n + 1 + 0 [MOD k] := by refine ModEq.add_left (↑n + 1) ?h; refine modEq_zero_iff_dvd.mpr ?_; exact Nat.dvd_mul_left (↑k) i

  -- prove that i-th number is  a(n) + 1 + i * k
  have nth_unfold (n : ℕ+) (i : ℕ) :
      Nat.nth {m | p n m} i = a n + 1 + i * k := by
    induction i with
    | zero =>
      simp
      obtain h := p_n_plus_1 n 0
      simp at h
      obtain ⟨i, ⟨hf, hi⟩⟩ := Nat.exists_lt_card_nth_eq h
      rw [<-hi]
      congr
      all_goals {
        by_contra hneq
        push_neg at hneq
        have hige0 : i > 0 := by exact one_le_iff_ne_zero.mpr (id (Ne.symm hneq))
        have hige0 : Nat.nth (p n) i > Nat.nth (p n) 0 := by exact nth_lt_nth' hige0 hf
        have hle : Nat.nth (p n) 0 < a n + 1 := by rw [<-hi]; exact hige0
        have hgt := (Nat.nth_mem_of_infinite (infinite n) 0).left
        have hnge : ¬ nth (p n) 0 > ↑(a n) := by push_neg; exact le_of_lt_succ hle
        contradiction
      }
    | succ i ih =>
      obtain h := p_n_plus_1 n (i + 1)
      obtain ⟨j, ⟨hf, hj⟩⟩ := Nat.exists_lt_card_nth_eq h
      rw [<-hj]
      congr
      by_contra hneq
      have ih : Nat.nth (p n) i = (a n) + 1 + i * ↑k := by rw [<-ih]; exact rfl
      rcases lt_or_gt_of_ne hneq with hlt | hgt
      · let c := Nat.nth (p n) (i + 1)
        have hclt : c < Nat.nth (p n) j := by exact nth_lt_nth' hlt hf
        have hcgt : c > Nat.nth (p n) i := by refine (nth_lt_nth (infinite n)).mpr ?_; exact lt_add_one i
        rw [hj] at hclt
        rw [ih] at hcgt
        have hcgt : c % k + c / k * k > (a n + 1) % k + (a n + 1) / k * k + i * k := by
          calc
            c % k + c / k * k = c := by exact mod_add_div' c ↑k
            _ > ↑(a n) + 1 + i * ↑k := by rel [hcgt]
            _ = (a n + 1) % k + (a n + 1) / k * k + i * k :=  by congr 1; exact Eq.symm (mod_add_div' (↑(a n) + 1) ↑k)
        have hclt : c % k + c / k * k < (a n + 1) % k + (a n + 1) / k * k + (i + 1) * k := by
          calc
            c % k + c / k * k = c := by exact mod_add_div' c ↑k
            _ < ↑(a n) + 1 + (i + 1) * ↑k := by rel [hclt]
            _ = (a n + 1) % k + (a n + 1) / k * k + (i + 1) * k :=  by congr 1; exact Eq.symm (mod_add_div' (↑(a n) + 1) ↑k)
        have hcmod := (Nat.nth_mem_of_infinite (infinite n) (i + 1)).right
        have han := (p_n_plus_1 n 0).right
        simp at han
        have : c ≡ (a n) + 1 [MOD k] := by exact ModEq.trans hcmod (id (ModEq.symm han))
        have : c % k = (a n + 1) % k := by exact this
        rw [this] at hcgt hclt
        rw [Nat.add_assoc] at hcgt hclt
        simp [Nat.add_right_inj] at hcgt hclt
        rw [<-Nat.add_mul] at hcgt hclt
        have hclt : c / k < (a n + 1) / k + i + 1 := by
          apply Nat.lt_of_mul_lt_mul_right hclt
        have hcgt : c / k > (a n + 1) / k + i := by
          apply Nat.lt_of_mul_lt_mul_right hcgt
        have hcgt : ¬ c / k < (a n + 1) / k + i + 1 := by push_neg; exact hcgt
        contradiction
      · have hjlei : j ≤ i := by exact le_of_lt_succ hgt
        have hjth : Nat.nth (p n) j ≤ Nat.nth (p n) i := by refine (nth_le_nth (infinite n)).mpr hjlei
        rw [hj, ih] at hjth
        have hile : i + 1 > i := by exact lt_add_one i
        have : ¬ ↑(a n) + 1 + (i + 1) * ↑k ≤ ↑(a n) + 1 + i * ↑k := by
          push_neg
          rel [hile]
        contradiction

  -- obtain that a (n + 1) = a(n) + 1 + n*k
  have get_recur (n : ℕ+) : a (n + 1) = a n + 1 + n * k := by
    apply PNat.coe_inj.mp
    rw [haₙ n, PNat.add_coe, PNat.add_coe, PNat.one_coe, PNat.mul_coe, <-nth_unfold n n]

  intro n

  -- solve the recurrence
  have solve_recur (haₙ : ∀ n, a (n + 1) = a n + 1 + n * k) : (a n).val = n * (n - 1) * k / 2 + n := by
    induction n using PNat.caseStrongInductionOn
    · simp [ha₁]
    · rename_i m ih
      rw [haₙ m]
      simp [ PNat.add_coe]
      rw [ih m (refl m)]
      ring_nf
      rw [Nat.add_assoc, Nat.add_right_inj]
      apply Nat.eq_div_of_mul_eq_right
      trivial
      rw [Nat.mul_add, Nat.mul_div_cancel', Nat.mul_sub, Nat.sub_mul, Nat.mul_one]
      rw [show (2 = 1 + 1) by decide, Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_right_inj]
      rw [Nat.add_sub_cancel']
      · ring
      · simp [Nat.mul_le_mul_right k]
        exact NeZero.one_le
      · apply Dvd.dvd.mul_right
        by_cases h : Even m.val
        · apply Dvd.dvd.mul_right
          exact even_iff_two_dvd.mp h
        · simp at h
          have : Even (m.val - 1) := by refine Nat.Odd.sub_odd h ?hn; trivial
          apply Dvd.dvd.mul_left
          exact even_iff_two_dvd.mp this

  exact solve_recur (fun n ↦ get_recur n)

theorem number_theory_8517_2 (hk : k = 2) (a : ℕ+ → ℕ+) (ha₁ : a 1 = 1) (haₙ : ∀ n, a (n + 1) = (Nat.nth {m | m > a n ∧ m ≡ (n + 1) [MOD k]} n)) :
    ∀ n, (a n).val = n * (n - 1) + n := by
  -- substitute k = 2
  simp [hk] at *
  intro n
  rw [number_theory_8517_1 2 a ha₁ haₙ]
  simp
