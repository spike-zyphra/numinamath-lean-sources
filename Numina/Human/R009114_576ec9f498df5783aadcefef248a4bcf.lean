import Mathlib

open Nat List

/-
PROBLEM: A finite sequence of three-digit integers has the property that the tens and units digits of each term are, respectively, the hundreds and tens digits of the next term, and the tens and units digits of the last term are, respectively, the hundreds and tens digits of the first term.
For example, such a sequence might begin with the terms 247, 475, and 756 and end with the term 824. Let $S$ be the sum of all the terms in the sequence. What is the largest prime factor that always divides $S$?
-/
theorem AMC_Number_Theory_1177  (hl1: List ℕ → Prop) (hhl1: ∀l, hl1 l = (∀n ∈ l, 100 ≤ n ∧ n ≤ 999))(R: Option ℕ → Option ℕ → Prop)
(hR: ∀m, ∀n, R m n = (match m with
| none => True
| some m' =>
  match n with
  | none => True
  | some n' => (m' % 100 / 10 = n' / 100 ∧ m' % 10 = n' % 100 / 10)))
  (hl2: List ℕ → Prop )(hhl2: ∀l, hl2 l = (∀i:ℕ, R l[i%l.length]? l[(i+1) % l.length]?)):
IsGreatest {p:ℕ | p.Prime ∧ ∀l:List ℕ, hl1 l → hl2 l → p ∣ l.sum} 37 := by
  --  Let S be the sum of all the terms in the sequence
  constructor
  · simp only [Set.mem_setOf_eq]
    constructor
    · exact properDivisors_eq_singleton_one_iff_prime.mp rfl
    · intro l hl1_this hl2_this

      let S:ℕ := l.sum

      let getHundreds : ℕ → ℕ := fun n => n / 100
      let getTens : ℕ → ℕ := fun n => n % 100/10
      let getUnits: ℕ → ℕ := fun n => n % 10

      let hundredsDigits : List ℕ := l.map getHundreds
      let tensDigits : List ℕ := l.map getTens
      let unitsDigits : List ℕ := l.map getUnits

      -- A given digit appears as the hundreds digit, the tens digit, and the units digit of a term the same number of times.
      have h1: hundredsDigits ~ tensDigits ∧ tensDigits ~ unitsDigits :=by
        rw [hhl2] at hl2_this

        have h1a: ∀i:ℕ, hundredsDigits[(i+1) % l.length]? = tensDigits[i % l.length]? := by
          intro i
          dsimp only [hundredsDigits, tensDigits]
          simp only [getElem?_map]
          have: R l[i % l.length]? l[(i + 1) % l.length]? := hl2_this i
          rw [hR] at this

          by_cases h:l.length = 0
          case pos =>
            have: l = [] := by exact length_eq_zero.mp h
            rw [this]
            simp
          case neg =>
            rw [l.getElem?_eq_getElem (i.mod_lt (zero_lt_of_ne_zero h))]
            rw [l.getElem?_eq_getElem ((i+1).mod_lt (zero_lt_of_ne_zero h))]
            rw [l.getElem?_eq_getElem (i.mod_lt (zero_lt_of_ne_zero h))] at this
            rw [l.getElem?_eq_getElem ((i+1).mod_lt (zero_lt_of_ne_zero h))] at this
            simp only at this
            simp only [Option.map_some', Option.some.injEq]
            dsimp only [getHundreds, getTens]
            rw [this.1]


        have h1b: ∀i:ℕ, tensDigits[(i+1) % l.length]? = unitsDigits[i % l.length]? := by
          intro i
          dsimp only [tensDigits, unitsDigits]
          simp only [getElem?_map]
          have: R l[i % l.length]? l[(i + 1) % l.length]? := hl2_this i
          rw [hR] at this

          by_cases h:l.length = 0
          case pos =>
            have: l = [] := by exact length_eq_zero.mp h
            rw [this]
            simp
          case neg =>
            rw [l.getElem?_eq_getElem (i.mod_lt (zero_lt_of_ne_zero h))]
            rw [l.getElem?_eq_getElem ((i+1).mod_lt (zero_lt_of_ne_zero h))]
            rw [l.getElem?_eq_getElem (i.mod_lt (zero_lt_of_ne_zero h))] at this
            rw [l.getElem?_eq_getElem ((i+1).mod_lt (zero_lt_of_ne_zero h))] at this
            simp only at this
            simp only [Option.map_some', Option.some.injEq]
            dsimp only [getTens, getUnits]
            rw [this.2]

        have: ∀l1 l2: List ℕ,l1.length = l2.length → (∀i:ℕ, l1[(i+1)% l1.length]? = l2[i % l2.length]?) → l1.rotate 1 = l2 := by
          intro l1 l2 h1 h2
          match l1 with
          | [] =>
              have: l2 = [] := by
                exact length_eq_zero.mp (id (Eq.symm h1))
              rw [this]
              simp
          | hd::tl =>
              have h3: (hd::tl).length > 0 := by exact zero_lt_succ tl.length
              have h4: l2.length > 0 := by exact Nat.lt_of_sub_eq_succ (id (Eq.symm h1))
              have h5: [hd].length = 1 := by exact rfl
              have h6: tl.length = l2.length - 1 := by
                rw [← h1]
                exact rfl
              rw [List.rotate_eq_rotate']
              simp only [rotate', append_eq_nil, cons_ne_self, and_false, imp_self, rotate'.eq_2]
              ext i n
              have h2:= h2 i
              rw [List.getElem?_cons] at h2
              by_cases h7:i<tl.length
              case pos =>
                rw [tl.getElem?_append_left h7]
                have: (i+1) % (hd::tl).length ≠  0 := by
                  have: (i+1) < (hd::tl).length := by exact add_lt_of_lt_sub h7
                  rw [Nat.mod_eq_of_lt]
                  simp only [ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false,
                    not_false_eq_true]
                  exact this
                simp only [this] at h2
                simp only [↓reduceIte, length_cons] at h2
                have: (i + 1) % (tl.length + 1)  = i + 1 := by
                  rw [Nat.mod_eq_of_lt]
                  simp only [add_lt_add_iff_right]
                  exact h7
                have h8: (i + 1) % (tl.length + 1) - 1 = i := by
                  exact Eq.symm (Nat.eq_sub_of_add_eq (id (Eq.symm this)))
                have h9: i % l2.length = i := by
                  have: l2.length = tl.length + 1 := by exact id (Eq.symm h1)
                  rw [this]
                  rw [Nat.mod_eq_of_lt]
                  exact Nat.lt_add_right 1 h7
                rw [h8, h9] at h2
                exact Eq.to_iff (congrFun (congrArg Membership.mem h2) n)

              case neg =>
                have h8: i = tl.length ∨ i > tl.length := by exact Nat.eq_or_lt_of_not_lt h7
                cases h8 with
                | inl h8 =>
                  have: (i + 1) % (hd :: tl).length = 0 := by
                    rw [h8]
                    exact mod_self (tl.length + 1)
                  simp only [this] at h2
                  simp only [↓reduceIte] at h2
                  rw [tl.getElem?_append_right (Nat.le_of_not_lt h7)]
                  simp only [h8, tsub_self, length_singleton, zero_lt_one, getElem?_eq_getElem,
                    getElem_cons_zero, Option.mem_def, Option.some.injEq]
                  have: i % l2.length = tl.length := by
                    rw [h8, h6]
                    exact self_sub_mod l2.length 1
                  rw [this] at h2
                  constructor
                  · intro h9
                    rw [h9] at h2
                    rw [h2]
                  · intro h9
                    rw [h9] at h2
                    exact ENat.coe_inj.mp h2

                | inr h8 =>
                  have: (tl ++ [hd])[i]? = none := by
                    have: i >= (tl ++ [hd]).length := by
                      rw [List.length_append]
                      simp only [length_singleton, ge_iff_le]
                      exact h8
                    exact getElem?_eq_none_iff.mpr this
                  rw [this]
                  have: l2[i]? = none := by
                    have: i>= l2.length := by
                      exact le_of_eq_of_le (id (Eq.symm h1)) h8
                    exact getElem?_eq_none_iff.mpr this
                  rw [this]

        have hundredsLength: hundredsDigits.length = l.length := by
          dsimp only [hundredsDigits]
          exact length_map l getHundreds
        have tensLength: tensDigits.length = l.length := by
          dsimp only [tensDigits]
          exact length_map l getTens
        have unitsLength: unitsDigits.length = l.length := by
          dsimp only [unitsDigits]
          exact length_map l getUnits

        have h1c: hundredsDigits.rotate 1 = tensDigits := by
          apply this hundredsDigits tensDigits
          · rw [hundredsLength, tensLength]
          · rw [hundredsLength, tensLength]
            exact h1a

        have h1d: tensDigits.rotate 1 = unitsDigits := by
          apply this tensDigits unitsDigits
          · rw [tensLength, unitsLength]
          · rw [tensLength, unitsLength]
            exact h1b

        constructor
        · rw [← h1c]
          exact Perm.symm (rotate_perm hundredsDigits 1)
        · rw [← h1d]
          exact Perm.symm (rotate_perm tensDigits 1)



      --  Let k be the sum of the units digits in all the terms
      let k :ℕ := unitsDigits.sum

      have h2: hundredsDigits.sum = tensDigits.sum ∧ tensDigits.sum = unitsDigits.sum := by
        exact ⟨List.Perm.sum_eq h1.1, List.Perm.sum_eq h1.2⟩

      -- Then S = 111k
      have h3: S = 111 * k := by
        have h3a: ∀n, 100 * (getHundreds n) + 10 * (getTens n) + 1 * (getUnits n) = n := by
          intro n
          dsimp only [getHundreds, getTens, getUnits]
          nth_rw 4 [← div_add_mod n 100]
          nth_rw 2 [← div_add_mod (n%100) 10]
          have: n % 100 % 10 = n % 10 := by exact mod_mul_right_mod n 10 10
          rw [this]
          ring_nf

        have h3b: l.map (fun n => 100 * (getHundreds n) + 10 * (getTens n) + 1 * (getUnits n)) = l := by
          ext i n
          simp only [getElem?_map, Option.mem_def, Option.map_eq_some']
          constructor
          · intro h
            rcases h with ⟨m, hm⟩
            rw [hm.1]
            simp only [Option.some.injEq]
            rw [h3a m] at hm
            exact hm.2
          · intro h
            use n
            constructor
            · exact h
            · rw [h3a n]


        have: S = 100 * hundredsDigits.sum + 10 * tensDigits.sum + 1 * unitsDigits.sum := by
          dsimp only [hundredsDigits, tensDigits, unitsDigits, S]
          have list_sum_linear_three: ∀l:List ℕ, ∀a b c:ℕ, ∀f g h:ℕ→ℕ , a * (l.map f).sum + b * (l.map g).sum + c * (l.map h).sum= (l.map (fun n => a * (f n) + b * (g n) + c * (h n))).sum := by
            intro l a b c f g h
            induction l with
            | nil => simp
            | cons hd tl htl =>
              simp only [map_cons, List.sum_cons]
              rw [← htl]
              ring_nf
          rw [list_sum_linear_three l 100 10 1 getHundreds getTens getUnits]
          rw [h3b]

        rw [h2.1, h2.2] at this
        rw [← distrib_three_right] at this
        simp only [reduceAdd] at this
        dsimp only [k]
        exact this

      -- S = 111k = 3 * 37 * k
      have h4: S = 3 * 37 * k := by
        simp only [reduceMul]
        exact h3

      -- so S must be divisible by 37
      have h5: 37 ∣ S := by
        rw [h4]
        rw [mul_comm, ← mul_assoc]
        exact Nat.dvd_mul_left 37 (k * 3)

      dsimp only [S] at h5
      exact h5

  · dsimp only [upperBounds]
    simp only [Set.mem_setOf_eq, and_imp]
    intro p pprime hp
    -- see that it need not be divisible by any larger prime
    apply (fun a => Nat.le_of_not_lt a:¬p> 37 → p≤37)
    intro pgt37

    -- the sequence 123, 231, 312
    let l : List ℕ := [123, 231, 312]
    let S : ℕ := l.sum

    -- the sequence 123, 231, 312 satisifies the conditions
    have hl1_this: hl1 l := by
      dsimp only [l]
      rw [hhl1]
      simp
    have hl2_this: hl2 l := by
      dsimp only [l]
      rw [hhl2]
      simp only [length_cons, length_singleton, reduceAdd]
      simp only [length_nil, zero_add, reduceAdd]
      intro i
      have: ∀n:ℕ, n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
        intro n
        have: n % 3 < 3 := by exact Nat.mod_lt n (by exact zero_lt_succ 2:3>0)
        rw [Nat.lt_succ_iff] at this
        apply Nat.lt_or_eq_of_le at this
        rw [← or_assoc]
        cases this with
        | inl hP =>
          left
          rw [Nat.lt_succ_iff] at hP
          apply Nat.lt_or_eq_of_le at hP
          rw [← Nat.lt_one_iff]
          exact hP
        | inr hQ =>
          right
          exact hQ
      cases this i with
      | inl hP =>
        have: (i+1) % 3 = 1 := by rw [Nat.add_mod, hP]
        rw [hP, this, hR]
        simp
      | inr hP =>
        cases hP with
        | inl hP =>
          have: (i+1) % 3 = 2 := by rw [Nat.add_mod, hP]
          rw [hP, this, hR]
          simp
        | inr hP =>
          have: (i+1) % 3 = 0 := by rw [Nat.add_mod, hP]
          rw [hP, this, hR]
          simp

    -- the sequence 123, 231, 312 gives S = 666
    have h1: S = 666 := by
      dsimp only [S, l]
      simp

    -- the sequence 123, 231, 312 gives S = 2 * 3 * 3 * 37
    have h2: S = 2 * 3 * 3 * 37 := by
      simp only [reduceMul]
      exact h1

    have h3: p ∣ S := by
      dsimp only [S]
      exact hp l hl1_this hl2_this

    have h4: p ∣ 2 * 3 * 3 * 37 := by rw [h2] at h3; exact h3

    have h5: S.primeFactors = {2, 3, 37} := by
      rw [h2]
      rw [Nat.primeFactors_mul (by simp) (by simp)]
      rw [Nat.primeFactors_mul (by simp) (by simp)]
      rw [Nat.primeFactors_mul (by simp) (by simp)]
      rw [Nat.Prime.primeFactors (by exact prime_two)]
      rw [Nat.Prime.primeFactors (by exact prime_three)]
      rw [Nat.Prime.primeFactors (by exact properDivisors_eq_singleton_one_iff_prime.mp rfl)]
      rfl


    -- it need not be divisible by any larger prime
    show False
    have : p ∈ S.primeFactors := by
      apply Nat.mem_primeFactors.mpr
      exact ⟨pprime, h3, Ne.symm (zero_ne_add_one (123 + 542))⟩
    rw [h5] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    cases this with
    | inl hP => rw [hP] at pgt37;  norm_num at pgt37
    | inr hP =>
      cases hP with
      | inl hP => rw [hP] at pgt37; norm_num at pgt37
      | inr hP => rw [hP] at pgt37; norm_num at pgt37