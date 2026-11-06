import Mathlib
open Mathlib

/--
Find the sum of all positive integers $a=2^n3^m$ where $n$ and $m$ are non-negative integers, for which $a^6$ is not a divisor of $6^a$.
-/

-- Code to compute final answer
def cnt (reviveM n m : ℕ) : ℕ :=
  match n, m with
  | 0, _ => 0
  | a + 1, 0 => cnt reviveM a reviveM
  | n + 1, m + 1 =>
    let a := 2^n * 3^m;
    (if ¬a^6 ∣ 6^a then a else 0) + cnt reviveM (n + 1) m

set_option synthInstance.maxHeartbeats 0
set_option maxHeartbeats 0

lemma numbertheory_721 (x : Finset ℕ) (h : ∀ a, a ∈ x ↔ (∃ n m, a = 2^n * 3^m) ∧ ¬a^6 ∣ 6^a) : ∑ a ∈ x, a = 42 := by
  -- Substitute $a=2^n3^m$ into $a^6$ and $6^a$, and find all pairs of non-negative integers (n,m) for which $(2^n3^m)^{6}$ is not a divisor of $6^{2^n3^m}$
  have step1 : ∀ a n m, a = 2^n * 3^m → ¬a^6 ∣ 6^a → 2^n * 3^m < 6 * n ∨ 2^n * 3^m < 6 * m := by
    intros a n m ha hb
    have ne01 : 2 ^ (6 * n) * 3 ^ (6 * m) ≠ 0 := by
      apply Nat.mul_ne_zero <;> apply pow_ne_zero <;> decide
    have ne02 : 2 ^ (2 ^ n * 3 ^ m) * 3 ^ (2 ^ n * 3 ^ m) ≠ 0 := by
      apply Nat.mul_ne_zero <;> apply pow_ne_zero <;> decide
    rw [ha, (by ring : (2 ^ n * 3 ^ m) ^ 6 = 2 ^ (6 * n) * 3 ^ (6 * m)), (by rw [← Nat.mul_pow] : 6 ^ (2 ^ n * 3 ^ m) = (2 ^ (2 ^ n * 3 ^ m)) * (3 ^ (2 ^ n * 3 ^ m))), ← Nat.factorization_le_iff_dvd ne01 ne02, Finsupp.le_def] at hb
    push_neg at hb
    cases' hb with i hb
    -- Comparing both exponents (noting that there must be either extra powers of 2 or extra powers of 3 in the left expression):
    -- $6n > 2^n3^m$  OR  $6m > 2^n3^m$
    by_cases h2 : i = 2
    · rw [h2] at hb
      simp only [ne_eq, mul_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and, or_self,
        not_false_eq_true, pow_eq_zero_iff, Nat.factorization_mul, Nat.factorization_pow,
        Finsupp.coe_add, Finsupp.coe_smul, nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
        Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.ofNat_apply, false_or, Pi.natCast_def,
        Nat.cast_id] at hb
      rw [(by native_decide : (Nat.factorization 3) 2 = 0), (by native_decide : (Nat.factorization 2) 2 = 1)] at hb
      norm_num at hb
      left; exact hb
    by_cases h3 : i = 3
    · rw [h3] at hb
      simp only [ne_eq, mul_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and, or_self,
        not_false_eq_true, pow_eq_zero_iff, Nat.factorization_mul, Nat.factorization_pow,
        Finsupp.coe_add, Finsupp.coe_smul, nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
        Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.ofNat_apply, false_or, Pi.natCast_def,
        Nat.cast_id] at hb
      rw [(by native_decide : (Nat.factorization 2) 3 = 0), (by native_decide : (Nat.factorization 3) 3 = 1)] at hb
      norm_num at hb
      right; exact hb
    simp only [ne_eq, mul_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and, or_self,
      not_false_eq_true, pow_eq_zero_iff, Nat.factorization_mul, Nat.factorization_pow,
      Finsupp.coe_add, Finsupp.coe_smul, nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.ofNat_apply, false_or, Pi.natCast_def,
      Nat.cast_id] at hb
    by_cases h2 : i = 1
    · rw [h2, (by native_decide : (Nat.factorization 2) 1 = 0), (by native_decide : (Nat.factorization 3) 1 = 0)] at hb
      norm_num at hb
    have zh2 : ¬i ∣ 2 := by
      intro gg
      have := Nat.Prime.eq_one_or_self_of_dvd (by decide) _ gg
      tauto
    have zh3 : ¬i ∣ 3 := by
      intro gg
      have := Nat.Prime.eq_one_or_self_of_dvd (by decide) _ gg
      tauto
    rw [Nat.factorization_eq_zero_of_not_dvd zh2, Nat.factorization_eq_zero_of_not_dvd zh3] at hb
    norm_num at hb
  -- We prove n < 6 if 2^n * 3^m < 6*n
  have geq1 : ∀ n m, n ≥ 6 → 2^n * 3^m ≥ 6 * n := by
    intros n m h
    induction n with
    | zero => linarith
    | succ n IH =>
      by_cases h1 : n = 5
      · rw [h1]
        norm_num
        have : 1 ≤ 3^m := by apply Nat.one_le_pow'
        linarith
      have s : n + 1 ≠ 6 := by
        intro ks
        apply h1
        linarith
      cases' (eq_or_lt_of_le h) with h h
      · exfalso; apply s; rw [h]
      have cc := IH (Nat.le_of_lt_succ h)
      rw [Nat.pow_succ]
      linarith
  -- We prove m < 2 if 2^n * 3^m < 6*n
  have geq11 : ∀ n m, m ≥ 2 → 2^n * 3^m ≥ 6 * n := by
    intros n m h
    induction n with
    | zero => norm_num
    | succ n IH =>
      norm_num
      rw [Nat.mul_succ, Nat.pow_succ]
      have jak := Nat.pow_le_pow_of_le (by decide : 1 < 3) h
      norm_num at jak
      have : 1 ≤ 2^n := by apply Nat.one_le_pow'
      have jsj := Nat.mul_le_mul this jak
      linarith
  -- We prove n < 2 if 2^n * 3^m < 6^m
  have geq21 : ∀ n m, n ≥ 2 → 2^n * 3^m ≥ 6 * m := by
    intros n m h
    induction m with
    | zero => norm_num
    | succ m IH =>
      norm_num
      rw [Nat.mul_succ, Nat.pow_succ]
      have jak := Nat.pow_le_pow_of_le (by decide : 1 < 2) h
      norm_num at jak
      have : 1 ≤ 3^m := by apply Nat.one_le_pow'
      have jsj := Nat.mul_le_mul this jak
      linarith
  -- We prove m < 5 if 2^n * 3^m < 6^m
  have geq2 : ∀ n m, m ≥ 5 → 2^n * 3^m ≥ 6 * m := by
    intros n m h
    induction m with
    | zero => linarith
    | succ m IH =>
      by_cases h1 : m = 4
      · rw [h1]
        have := Nat.one_le_pow' n 1
        norm_num at this
        norm_num
        linarith
      have s : m + 1 ≠ 5 := by
        intro g
        apply h1
        linarith
      cases' (eq_or_lt_of_le h) with h h
      · exfalso; apply s; rw [h]
      have cc := IH (Nat.le_of_lt_succ h)
      rw [Nat.pow_succ]
      linarith
  have tightened : ∀ (a : ℕ), a ∈ x ↔ (∃ n m, a = 2 ^ n * 3 ^ m ∧ (n < 6 ∧ m < 5)) ∧ ¬a ^ 6 ∣ 6 ^ a := by
    -- Start of proof for the forward direction: "If a ∈ x, then the conditions are satisfied."
    intro a
    constructor <;> intro h1
    
    -- First case: Prove the existence of n and m such that the conditions are met
    · rw [h] at h1    -- Rewrite the hypothesis h based on assumption that a ∈ x
      cases' h1 with h12 h13    -- Break down the structure of h1
      cases' h12 with n h12    -- Break h12 to get n
      cases' h12 with m h12    -- Break h12 further to get m
      constructor    -- Prove the existential statement: there exist n and m
      · exists n    -- Claim n exists
        exists m    -- Claim m exists
        constructor    -- We now prove the conditions on n and m
        · exact h12    -- Prove that a = 2^n * 3^m holds as per the original hypothesis
        
        -- Step for the additional condition ¬a^6 ∣ 6^a
        have stp2 := step1 a n m h12 h13    -- Use step1 to get further info about a, n, and m
        constructor    -- Prove further conditions
        · by_cases h22 : n < 6    -- Case analysis: Check if n < 6
          · exact h22    -- If n < 6, the condition holds directly
          cases' stp2 with stp2 stp2    -- Otherwise, use the contradiction from step2
          · have := Nat.not_lt_of_le (geq1 n m (Nat.le_of_not_lt h22))    -- Case for contradiction
            exfalso    -- Derive a contradiction
            exact this stp2    -- Use the contradiction to prove the statement
          · have akd := geq21 n m    -- Use geq21 to generate a new argument for the contradiction
            rw [← Decidable.not_imp_not] at akd    -- Manipulate with logical equivalence
            rw [Nat.not_le, Nat.not_le] at akd    -- Further manipulation
            exact Nat.lt_trans (akd stp2) (by decide : 2 < 6)    -- Conclude with the transitivity of inequalities
            
        -- Step for condition m < 5
        · by_cases h22 : m < 5    -- Case analysis: Check if m < 5
          · exact h22    -- If m < 5, the condition holds directly
          cases' stp2 with stp2 stp2    -- Otherwise, use the contradiction from step2
          · have := Nat.not_lt_of_le (geq11 n m (Nat.le_trans (by decide : 2 ≤ 5) (Nat.le_of_not_lt h22)))    -- Similar contradiction for m
            exfalso    -- Derive a contradiction
            exact this stp2    -- Use the contradiction to prove the statement
          · have akd := geq2 n m    -- Use geq2 to generate a new argument for the contradiction
            rw [← Decidable.not_imp_not] at akd    -- Manipulate with logical equivalence
            rw [Nat.not_le, Nat.not_le] at akd    -- Further manipulation
            exact akd stp2    -- Conclude with the contradiction for m            
      -- Final condition to prove ¬a^6 ∣ 6^a
      · exact h13    -- Simply use h13 to complete the proof

    -- Second case: Prove the backward direction: "If the conditions hold, then a ∈ x."
    cases' h1 with h1 h2    -- Break down the hypothesis
    cases' h1 with n h1    -- Extract n from the hypothesis
    cases' h1 with m h1    -- Extract m from the hypothesis
    cases' h1 with h12 h13    -- Break further down to get conditions on n and m
    rw [h]    -- Rewrite based on the assumption that a ∈ x
    constructor    -- Now prove that a ∈ x
    · exists n    -- Existence of n
      exists m    -- Existence of m
    · assumption    -- Assume the necessary conditions hold based on previous steps
  -- Prove the algorithm can calculate the sum
  have sub : ∀ (reviveM maxN maxM : ℕ) (b : maxM ≤ reviveM) (s : Finset ℕ) (h : ∀ (a : ℕ), a ∈ s ↔ (∃ n m, a = 2 ^ n * 3 ^ m ∧ ((n + 1 < maxN ∧ m < reviveM) ∨ (n + 1 = maxN ∧ m < maxM))) ∧ ¬a ^ 6 ∣ 6 ^ a), ∑ x ∈ s, x = cnt reviveM maxN maxM := by
    intros reviveM maxN maxM
    induction maxN, maxM using cnt.induct reviveM with
    | case1 m =>
      intros b s hs
      simp only [not_lt_zero', AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, false_and,
        or_false, false_or, cnt, Finset.sum_eq_zero_iff]
      intros x hmem
      rw [hs] at hmem
      cases' hmem with h1 h2
      cases' h1 with n h1
      cases' h1 with mm h1
      cases' h1 with h1 h2
      cases' h2 with h2 h2
      · linarith
      · linarith
    | case2 a ih1 =>
      intros hdjw s hc
      simp only [Nat.succ_eq_add_one, cnt]
      apply ih1
      · rfl
      intro ll
      rw [hc]
      constructor <;> intro uj <;> cases' uj with uj il <;> cases' uj with nn uj <;> cases' uj with mm uj <;> cases' uj with ua ub <;> cases' ub with uc ud; cases' uc with ue uf <;> constructor <;> (try assumption) <;> exists nn <;> exists mm
      · constructor <;> try assumption
        cases' Nat.eq_or_lt_of_le (Nat.le_of_lt_succ ue) with rs rs
        · right; tauto
        · left; tauto
      · constructor <;> try assumption
        exists nn; exists mm
        linarith
      · constructor <;> try assumption
        exists nn; exists mm
        constructor <;> try assumption
        left
        constructor <;> linarith
      · constructor <;> try assumption
        exists nn; exists mm
        constructor <;> try assumption
        left
        constructor <;> linarith
    | case3 n m ih1 =>
      simp only [Nat.succ_eq_add_one, Nat.reduceLeDiff, add_lt_add_iff_right, add_left_inj, cnt,
        ite_not]
      intros hm hs ha
      have decinst := fun a => Classical.propDecidable ((∃ n_1 m_1, a = 2 ^ n_1 * 3 ^ m_1 ∧ (n_1 < n ∧ m_1 < reviveM ∨ n_1 = n ∧ m_1 < m)) ∧ ¬a ^ 6 ∣ 6 ^ a)
      have taa := Finset.sum_filter_add_sum_filter_not hs (fun a => (∃ n_1 m_1, a = 2 ^ n_1 * 3 ^ m_1 ∧ (n_1 < n ∧ m_1 < reviveM ∨ n_1 = n ∧ m_1 < m)) ∧ ¬a ^ 6 ∣ 6 ^ a) (fun x => x)
      have prosl : (∀ (a : ℕ), a ∈ Finset.filter (fun a ↦ (∃ n_1 m_1, a = 2 ^ n_1 * 3 ^ m_1 ∧ (n_1 < n ∧ m_1 < reviveM ∨ n_1 = n ∧ m_1 < m)) ∧ ¬a ^ 6 ∣ 6 ^ a) hs ↔ (∃ n_1 m_1, a = 2 ^ n_1 * 3 ^ m_1 ∧ (n_1 + 1 < n + 1 ∧ m_1 < reviveM ∨ n_1 + 1 = n + 1 ∧ m_1 < m)) ∧ ¬a ^ 6 ∣ 6 ^ a) := by
        intro a
        rw [Finset.mem_filter, ha]
        constructor <;> intro hh
        · cases' hh with hh1 hh
          cases' hh with hh ee
          constructor <;> try assumption
          cases' hh with nn hh
          cases' hh with mm hh
          exists nn; exists mm
          constructor <;> try tauto
          cases' hh with hl hr
          cases' hr with hr hr
          · left; constructor <;> try tauto
            rw [Nat.add_one_lt_add_one_iff]; tauto
          · right; constructor <;> try tauto
        · cases' hh with hh hh1
          cases' hh with nn hh
          cases' hh with mm hh
          constructor <;> constructor <;> (try assumption) <;> exists nn <;> exists mm
          · cases' hh with hl hr
            constructor
            · exact hl
            cases' hr with hr hr <;> cases' hr with hr1 hr2
            · left
              constructor
              · rw [Nat.add_one_lt_add_one_iff] at hr1
                exact hr1
              · exact hr2
            · right
              constructor
              · rw [Nat.add_one_inj] at hr1
                exact hr1
              · apply Nat.lt_add_one_of_lt; exact hr2
          · cases' hh with hl hr
            constructor
            · exact hl
            cases' hr with hr hr <;> cases' hr with hr1 hr2
            · left
              constructor
              · rw [Nat.add_one_lt_add_one_iff] at hr1
                exact hr1
              · exact hr2
            · right
              constructor
              · rw [Nat.add_one_inj] at hr1
                exact hr1
              · exact hr2
      have jdj := ih1 (Nat.le_of_lt (Nat.lt_of_add_one_le hm)) (Finset.filter (fun a => (∃ n_1 m_1, a = 2 ^ n_1 * 3 ^ m_1 ∧ (n_1 < n ∧ m_1 < reviveM ∨ n_1 = n ∧ m_1 < m)) ∧ ¬a ^ 6 ∣ 6 ^ a) hs) prosl
      rw [jdj] at taa
      by_cases jks : (2 ^ n * 3 ^ m) ^ 6 ∣ 6 ^ (2 ^ n * 3 ^ m)
      · rw [if_pos jks]
        have emp : Finset.filter
          (fun x ↦ ¬((∃ n_1 m_1, x = 2 ^ n_1 * 3 ^ m_1 ∧ (n_1 < n ∧ m_1 < reviveM ∨ n_1 = n ∧ m_1 < m)) ∧ ¬x ^ 6 ∣ 6 ^ x)) hs = ∅ := by
          apply Finset.eq_empty_of_forall_not_mem
          intros x la
          rw [Finset.mem_filter] at la
          rw [ha] at la
          cases' la with l1 ll
          cases' l1 with ald l1
          cases' ald with nn ald
          cases' ald with mm ald
          cases' ald with al1 al2
          push_neg at ll
          cases' al2 with al2 al2
          · apply l1
            apply ll
            exists nn
            exists mm
            constructor
            · exact al1
            · left
              exact al2
          · cases' al2 with al2 al3
            rw [al2] at al1
            by_cases ud : mm = m
            · rw [ud] at al1
              simp only [al1] at l1
              apply l1
              exact jks
            have := Nat.eq_or_lt_of_le (Nat.le_of_lt_succ al3)
            cases' this with kds kds
            · exact (ud kds)
            apply l1
            apply ll
            exists nn
            exists mm
            constructor
            · rw [al2]
              exact al1
            · right
              constructor
              · exact al2
              · exact kds
        rw [emp] at taa
        norm_num at taa
        norm_num
        rw [taa]
      · rw [if_neg jks]
        have sig : Finset.filter
          (fun x ↦ ¬((∃ n_1 m_1, x = 2 ^ n_1 * 3 ^ m_1 ∧ (n_1 < n ∧ m_1 < reviveM ∨ n_1 = n ∧ m_1 < m)) ∧ ¬x ^ 6 ∣ 6 ^ x)) hs = { 2^n * 3^m } := by
          -- Start by proving that the filter operation on a Finset gives the singleton { 2^n * 3^m }
          rw [Finset.eq_singleton_iff_unique_mem]  -- Using the fact that a Finset is a singleton if and only if there is a unique element in it
          constructor  -- Proving the bi-implication: proving both directions of the equality

          -- First direction: Proving that if `x` satisfies the condition, then `x = 2^n * 3^m`
          · rw [Finset.mem_filter]  -- Check the element membership in the filter
            push_neg  -- Push the negation inside, turning the `¬` into a disjunction
            rw [ha]  -- Rewrite based on assumption `ha`
            constructor  -- Introduce the constructor for the disjunction
            · constructor  -- Introduce the conjunction for the existence of `n` and `m`
              · exists n
                exists m
                constructor  -- Proving that `x = 2^n * 3^m`
                · rfl  -- By reflexivity, `x = 2^n * 3^m`
                · right  -- Prove the second part of the disjunction
                  constructor
                  · rfl  -- `n = n` (trivially true)
                  · apply Nat.lt_add_one  -- Use the fact that `m < reviveM` to apply the inequality
              · exact jks  -- Use `jks` (likely another hypothesis or assumption) to conclude this part

            · intro wkd  -- Suppose there is a counterexample `wkd`
              cases' wkd with nn wkd  -- Break down `wkd` into the components of `n` and `m`
              cases' wkd with mm wkd  -- Break down `wkd` further for `m`
              cases' wkd with wkd wke  -- Further breakdown of the properties
              have wlc : (2 ^ n * 3 ^ m).factorization 2 = (2 ^ n * 3 ^ m).factorization 2 := rfl  -- Factorization equality for the prime 2
              conv at wlc =>  -- Apply the conversion to manipulate the factorization
                lhs
                rw [wkd]  -- Use `wkd` (which contains the decomposition) in the rewrite
              -- Simplify using various factorization properties
              simp only [ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and, not_false_eq_true,
                Nat.factorization_mul, Nat.factorization_pow, Finsupp.coe_add, Finsupp.coe_smul, nsmul_eq_mul,
                Pi.natCast_def, Nat.cast_id, Pi.add_apply, Pi.mul_apply, (by native_decide : (Nat.factorization 2) 2 = 1), 
                (by native_decide : (Nat.factorization 3) 3 = 1), (by native_decide : (Nat.factorization 3) 2 = 0), 
                (by native_decide : (Nat.factorization 2) 3 = 0)] at wlc  -- Perform the simplifications on `wlc`
              norm_num at wlc  -- Normalize numbers to simplify

              -- Do the same for factorization with respect to prime 3
              have wld : (2 ^ n * 3 ^ m).factorization 3 = (2 ^ n * 3 ^ m).factorization 3 := rfl
              conv at wld =>
                lhs
                rw [wkd]  -- Use `wkd` to rewrite the factorization
              -- Simplify similarly as before
              simp only [ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and, not_false_eq_true,
                Nat.factorization_mul, Nat.factorization_pow, Finsupp.coe_add, Finsupp.coe_smul, nsmul_eq_mul,
                Pi.natCast_def, Nat.cast_id, Pi.add_apply, Pi.mul_apply, (by native_decide : (Nat.factorization 2) 2 = 1), 
                (by native_decide : (Nat.factorization 3) 3 = 1), (by native_decide : (Nat.factorization 3) 2 = 0), 
                (by native_decide : (Nat.factorization 2) 3 = 0)] at wld
              norm_num at wld
              simp only [wlc, wld] at wke  -- Simplify using both factorizations
              cases' wke with wke wke  -- Break `wke` into two cases
              -- Case 1: `n` is not valid
              · cases' wke with wk1 wk2
                exfalso
                apply Nat.lt_irrefl n  -- Show that `n` cannot be less than itself
                exact wk1  -- Use `wk1` to arrive at the contradiction

              -- Case 2: `m` is not valid
              · cases' wke with wk1 wk2
                exfalso
                apply Nat.lt_irrefl m  -- Show that `m` cannot be less than itself
                exact wk2  -- Use `wk2` to arrive at the contradiction

          -- Second direction: Prove that if `x = 2^n * 3^m` then it satisfies the conditions
          · intros x hmem  -- Assume `x` is in the set defined by the filter
            rw [Finset.mem_filter, ha] at hmem  -- Use the assumption `ha`
            push_neg at hmem  -- Push the negation to break the condition
            cases' hmem with hml hmr  -- Break into two parts
            cases' hml with hml hmh  -- Further breakdown
            cases' hml with nn hml
            cases' hml with mm hml
            cases' hml with hmm hlm
            cases' hlm with hlm hlm
            -- First case: contradiction by `hmh` and `hmr`
            · exfalso
              apply hmh
              apply hmr
              exists nn
              exists mm
              constructor
              · exact hmm
              · left
                exact hlm

            -- Second case: handle the inequality case for `m`
            · cases' hlm with hle hlf
              have uwl := Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hlf)  -- Use `Nat.eq_or_lt_of_le` to break down the condition
              cases' uwl with uwl uwl  -- Break into two cases
              · rw [hle, uwl] at hmm  -- Use the inequality to prove a contradiction
                exact hmm

              -- Third case: contradiction by `hmh` and `hmr` using `nn` and `mm`
              · exfalso
                apply hmh
                apply hmr
                exists nn
                exists mm
                constructor
                · exact hmm
                · right
                  tauto  -- Use `tauto` to simplify the proof by automatically resolving logical tautologies

        -- Finally, we complete the proof by simplifying the sum of a singleton Finset
        rw [sig, Finset.sum_singleton] at taa  -- Apply the equality for the singleton sum
        rw [← taa]  -- Use the equality to conclude
        ring  -- Simplify the expression using ring tactics
  have appied := sub 5 6 5 (by decide)
  have subrw : ∀ n m, (n + 1 < 6 ∧ m < 5 ∨ n + 1 = 6 ∧ m < 5) ↔ n < 6 ∧ m < 5 := by
    -- Introduce variables n and m
    intros n m
    -- Clear any irrelevant hypotheses (since we're starting fresh for this proof)
    clear * -

    -- Start the proof of the bi-implication (↔): prove both directions of the equivalence.
    constructor <;> intro h1
    
    -- First case: Prove the forward direction: 
    -- If `n + 1 < 6 ∧ m < 5 ∨ n + 1 = 6 ∧ m < 5`, then `n < 6 ∧ m < 5`
    · cases' h1 with h1 h1    -- Break down the disjunction into two cases
      -- Case 1: `n + 1 < 6 ∧ m < 5`
      -- We need to show `n < 6 ∧ m < 5`
      · cases' h1 with h12 h13    -- Extract the two parts of the conjunction
        constructor <;> linarith    -- Use linear arithmetic (linarith) to prove `n < 6` and `m < 5`
      
      -- Case 2: `n + 1 = 6 ∧ m < 5`
      -- We need to show `n < 6 ∧ m < 5`
      · cases' h1 with h12 h13    -- Extract the two parts of the conjunction
        constructor <;> linarith    -- Use linear arithmetic to prove `n < 6` and `m < 5`
    
    -- Second case: Prove the backward direction:
    -- If `n < 6 ∧ m < 5`, then `n + 1 < 6 ∧ m < 5 ∨ n + 1 = 6 ∧ m < 5`
    · cases' h1 with h12 h13    -- Break the assumption `n < 6 ∧ m < 5` into two parts
      -- Use `Nat.eq_or_lt_of_le` to break `n < 6` into two cases
      cases' Nat.eq_or_lt_of_le (Nat.le_of_lt_succ h12) with h12 h12
      
      -- Case 1: `n + 1 < 6`
      -- This implies `n + 1 < 6 ∧ m < 5`
      · right    -- Use `right` to show `n + 1 = 6 ∧ m < 5`
        constructor    -- We prove the two parts of the conjunction
        · rw [h12]    -- `n + 1 = 6`
        · exact h13    -- `m < 5` holds directly from the assumption

      -- Case 2: `n + 1 = 6`
      -- This implies `n + 1 = 6 ∧ m < 5`
      · left    -- Use `left` to show `n + 1 < 6 ∧ m < 5`
        constructor    -- We prove the two parts of the conjunction
        · linarith    -- `n < 6` is implied by `n + 1 = 6`
        · exact h13    -- `m < 5` holds directly from the assumption`
  simp_rw [subrw] at appied
  have := appied _ tightened
  rw [(by native_decide : cnt 5 6 5 = 42)] at this
  exact this