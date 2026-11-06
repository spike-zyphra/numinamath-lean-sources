import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 0

/-
  $13$  fractions are corrected by using each of the numbers  $1,2,...,26$  once.
  **Example:** $\frac{12}{5},\frac{18}{26}.... $ What is the maximum number of fractions which are integers?
-/

theorem number_theory_8549 :
    IsGreatest {n | ∃ f : Fin 26 → ℕ, Function.Injective f ∧ (∀ x, f x ≥ 1 ∧ f x ≤ 26) ∧
    (Finset.filter (fun i ↦ f i % f (i + 13) = 0) (Finset.Icc 0 12)).card = n} 12 := by

  -- prove 12 can be obtained
  have case_eq_12 : ∃ f, Function.Injective f ∧ (∀ (x : Fin 26), 1 ≤ f x ∧ f x ≤ 26) ∧
      (Finset.filter (fun i ↦ f i % f (i + 13) = 0) (Finset.Icc 0 12)).card = 12 := by
    -- construct f explicitly
    let f (x : Fin 26) :=
      match x with
      | 0 => 23
      | 1 => 14
      | 2 => 15
      | 3 => 24
      | 4 => 25
      | 5 => 12
      | 6 => 21
      | 7 => 16
      | 8 => 18
      | 9 => 20
      | 10 => 22
      | 11 => 26
      | 12 => 17
      | 13 => 1
      | 14 => 2
      | 15 => 3
      | 16 => 4
      | 17 => 5
      | 18 => 6
      | 19 => 7
      | 20 => 8
      | 21 => 9
      | 22 => 10
      | 23 => 11
      | 24 => 13
      | 25 => 19
      | _ => 0

    -- construct left inverse of f
    let g (x : ℕ) : Fin 26 :=
      match x with
      | 0 => 0
      | 1 => 13
      | 2 => 14
      | 3 => 15
      | 4 => 16
      | 5 => 17
      | 6 => 18
      | 7 => 19
      | 8 => 20
      | 9 => 21
      | 10 => 22
      | 11 => 23
      | 12 => 5
      | 13 => 24
      | 14 => 1
      | 15 => 2
      | 16 => 7
      | 17 => 12
      | 18 => 8
      | 19 => 25
      | 20 => 9
      | 21 => 6
      | 22 => 10
      | 23 => 0
      | 24 => 3
      | 25 => 4
      | 26 => 11
      | _ => 0

    -- prove f is injective using g
    have f_inj : Function.Injective f := by
      apply Function.injective_iff_hasLeftInverse.mpr
      use g
      simp [Function.LeftInverse, f, g]
      intro x
      fin_cases x
      all_goals simp

    -- prove f induces 12 integers
    use f
    split_ands
    · exact f_inj
    · intro x
      simp [f]
      fin_cases x
      all_goals simp
    · let s := Finset.filter (fun i ↦ f i % f (i + 13) = 0) (Finset.Icc 0 12)
      let h (x : ℕ) (_ : x < 12) : Fin 26 := x
      have hf (a : Fin 26) (ha : a ∈ s) : ∃ i, ∃ (hlt : i < 12), h i hlt = a := by
        have : a < 12 := by
          simp [s] at ha
          obtain h := ha.left
          have : a ≠ 12 := by
            by_contra heq
            have h := ha.right
            rw [heq] at h
            simp [f] at h
          exact lt_of_le_of_ne h this
        use a, this
        simp [h]
      have hf' (i : ℕ) (h_1 : i < 12) : h i h_1 ∈ s := by
        simp [h, s]
        constructor
        · have : i ≤ 12 := by exact le_of_succ_le h_1
          have h : ((12 : ℕ) : Fin 26) = (12 : Fin 26) := by exact rfl
          rw [<-h]
          refine Fin.natCast_mono ?left.hbn this
          linarith
        · simp [f]
          interval_cases i
          all_goals
          simp
      have h_inj (i j : ℕ) (hi : i < 12) (hj : j < 12) (heq : h i hi = h j hj) : i = j := by
        simp [h] at heq
        apply Fin.val_inj.mpr at heq
        simp at heq
        have : i % 26 = i := by apply mod_eq_of_lt; linarith
        rw [this] at heq
        have : j % 26 = j := by apply mod_eq_of_lt; linarith
        rw [this] at heq
        exact heq
      exact Finset.card_eq_of_bijective h hf hf' h_inj

  simp [IsGreatest, upperBounds]
  constructor
  · exact case_eq_12
  · intro n f hf hrange hint
    -- prove n ≤ 13
    have ub : (Finset.filter (fun i ↦ f i % f (i + 13) = 0) (Finset.Icc 0 12)).card ≤ (Finset.Icc 0 12).card := by
      exact Finset.card_filter_le (Finset.Icc 0 12) fun i ↦ f i % f (i + 13) = 0
    simp at ub
    rw [hint] at ub
    rcases lt_or_eq_of_le ub with hlt | heq
    · -- if n ≤ 12, done
      exact le_of_lt_succ hlt
    · -- if n = 13, by contradiction
      rw [heq] at hint
      -- prove f is surjection
      have hint : Finset.filter (fun i ↦ f i % f (i + 13) = 0) (Finset.Icc 0 12)= Finset.Icc 0 12 := by
        apply Finset.eq_of_subset_of_card_le
        · exact Finset.filter_subset (fun i ↦ f i % f (i + 13) = 0) (Finset.Icc 0 12)
        · rw [hint]
          norm_cast
      apply Finset.filter_eq_self.mp at hint
      have hsub : Finset.image f (Finset.Icc (0 : Fin 26) 25) ⊆ Finset.Icc 1 26 := by
        intro y hy
        simp at hy
        obtain ⟨x, hx⟩ := hy
        obtain h := hrange x
        rw [hx.right] at h
        simp
        exact h
      have hcard : (Finset.image f (Finset.Icc (0 : Fin 26) 25)).card = (Finset.Icc (0 : Fin 26) 25).card := by
        apply Finset.card_image_of_injective _ hf
      have hcard' : (Finset.Icc (0 : Fin 26) 25).card = 26 := by
        norm_cast
      rw [hcard'] at hcard
      have : (Finset.Icc 1 26).card ≤ (Finset.image f (Finset.Icc (0 : Fin 26) 25)).card := by
        simp [hcard]
      have heq : Finset.image f (Finset.Icc (0 : Fin 26) 25) = Finset.Icc 1 26 := by
        apply Finset.eq_of_subset_of_card_le hsub this

      -- consider preimage of 17 19
      have case_17 : 17 ∈ Finset.Icc 1 26 := by norm_num
      have case_19 : 19 ∈ Finset.Icc 1 26 := by norm_num

      -- show that 17 / 19 must by coupled with 1
      have big_prime (x : Fin 26) (hp : Nat.Prime (f x)) (hx : f x > 13) : f (x + 13) = 1 := by
        by_cases hx : x ≤ 12
        · have : x ∈ Finset.Icc 0 12 := by simp; exact hx
          apply hint at this
          have : f (x + 13) ∣ f x := by apply Nat.dvd_of_mod_eq_zero this
          have : f (x + 13) = 1 ∨ f (x + 13) = f x := by
            apply Nat.dvd_prime hp |>.mp this
          rcases this with heq1 | heq
          · exact heq1
          · apply hf at heq
            simp at heq
        · push_neg at hx
          have : x - 13 ∈ Finset.Icc 0 12 := by
            revert hx
            fin_cases x
            all_goals simp
          apply hint at this
          simp at this
          have hdvd : f x ∣ f (x - 13) := by apply Nat.dvd_of_mod_eq_zero this
          have h1 : f (x - 13) ≤ 26 := by apply (hrange (x - 13)).right
          have h2 : f (x - 13) ≥ 1 := by apply (hrange (x - 13)).left
          have h3 : f x ≤ 26 := by apply (hrange x).right
          have : Nat.Prime (f x) → f x ∣ f (x - 13) → f (x - 13) = f x := by
            interval_cases f x
            all_goals
            interval_cases f (x - 13)
            all_goals decide
          apply this hp at hdvd
          apply hf at hdvd
          simp at hdvd

      -- hence, f (x17 + 13) = f (x19 + 13) = 1 → x17 + 13 = x19 + 13
      simp [<-heq] at case_17 case_19
      obtain ⟨x17, h17⟩ := case_17
      obtain ⟨x19, h19⟩ := case_19
      have h17' := big_prime x17 (show Nat.Prime (f x17) by rw [h17.right]; decide) (show f x17 > 13 by rw [h17.right]; simp)
      have h19' := big_prime x19 (show Nat.Prime (f x19) by rw [h19.right]; decide) (show f x19 > 13 by rw [h19.right]; simp)
      rw [<-h17'] at h19'
      apply hf at h19'
      -- x17 = x19 → f x17 = f x19, i.e., 17 = 19, contradiction
      simp at h19'
      apply congrArg f at h19'
      simp [h17.right, h19.right] at h19'
