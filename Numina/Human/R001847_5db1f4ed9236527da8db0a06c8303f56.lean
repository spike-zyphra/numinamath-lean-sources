import Mathlib

lemma l₁ {n} : 1 < n ∧ n < 10 → ¬n ≡ 1 [MOD 9] := by
  rintro ⟨ n_gt, n_lt ⟩ n_congr
  interval_cases n
  all_goals
    contrapose! n_congr
    decide

lemma l₂ {n} : 0 < n → n < 9 → ¬9 ∣ n := by
  rintro pos_n n_lt ⟨ k, k_eq ⟩
  simp_all

theorem Nat.digits_sum_0 {n b : ℕ} : b ≠ 0 →
  (∀ x ∈ Nat.digits b n, x = 0) → n = 0 := by
  intro b_ne_0 digits_0
  have := List.sum_eq_zero digits_0

  let l := (b.digits n).length
  have repl : l = (b.digits n).length ∧ ∀ x ∈ b.digits n, x = 0 :=
    ⟨ by simp [l], digits_0 ⟩
  rw [<- List.eq_replicate_iff] at repl
  rw [repl] at this
  apply congrArg (Nat.ofDigits b) at repl
  convert repl
  · exact Eq.symm (ofDigits_digits b n)
  · induction' (b.digits n).length with m ih
    · simp
    · simp [List.replicate_add, b.ofDigits_append]
      exact ih

lemma filter_replicate {α : Type*} [DecidableEq α]
  {s : Multiset α} {x : α} :
  s.filter (· = x) = Multiset.replicate (s.count x) x := by
  exact Multiset.filter_eq' s x

lemma digits_le {n}
  (binary_digits : ∀ d ∈ Nat.digits 10 n, d = 0 ∨ d = 1)
  (sum_lt : 9 ≤ (Nat.digits 10 n).sum)
  : Multiset.replicate 9 1 ≤ Nat.digits 10 n ∧
    (Nat.digits 10 n : Multiset ℕ).count 1 =
    (Nat.digits 10 n : Multiset ℕ).sum
   := by
  have sum_eq_filter : ((Nat.digits 10 n) : Multiset ℕ).sum =
    (((Nat.digits 10 n) : Multiset ℕ).filter λ x => x = 1).sum := by
    rw [<- Multiset.sum_filter_add_sum_filter_not (· = 1)]
    have : Multiset.filter (fun a ↦ ¬a = 1) ↑(Nat.digits 10 n) =
        Multiset.filter (fun a ↦ a = 0) ↑(Nat.digits 10 n) := by

      congr! 1 with x x_in
      specialize binary_digits x x_in
      cases binary_digits
      all_goals
        subst x
        simp
    rw [this]
    replace : (Multiset.filter (fun a ↦ a = 0) ↑(Nat.digits 10 n)).sum = 0 := by
      have : ∀ x ∈ List.filter (fun b ↦ decide (b = 0)) (Nat.digits 10 n), x = 0 := by
        simp
      exact List.sum_eq_zero this
    simp [this]
    exact this
  generalize hd : (Nat.digits 10 n : Multiset ℕ) = ds at *
  replace sum_lt : 9 ≤ ds.sum := by
    exact le_of_eq_of_le' (congrArg Multiset.sum hd) sum_lt

  replace binary_digits : ∀ d ∈ (Nat.digits 10 n : Multiset ℕ), d = 0 ∨ d = 1 := binary_digits
  have := by
    rw [<- Multiset.filter_eq_self (p := λ d => d = 0 ∨ d = 1)]
      at binary_digits
    simpa using binary_digits

  have count_eq : ds.count 1 = ds.sum := by
    rw [sum_eq_filter]
    have : Multiset.filter (fun x ↦ 1 = x) ds =
        (Multiset.filter (fun x ↦ x = 1) ds) := by
      congr
      ext x
      rw [Eq.comm]

    have : (Multiset.filter (fun x ↦ x = 1) ds).sum = ds.count 1 := by
      rw [Multiset.filter_eq']
      simp
    rw [<- this]

  refine And.intro ?_ count_eq
  suffices (Multiset.replicate 9 1).count 1 ≤ ds.count 1 by
    exact Multiset.le_count_iff_replicate_le.mp this
  conv_lhs => simp
  rw [count_eq]
  exact sum_lt


theorem number_theory_39481 :
    IsLeast {n : ℕ | 0 < n ∧ (∀ d ∈ Nat.digits 10 n, d = 0 ∨ d = 1) ∧ 225 ∣ n} 11111111100 := by
  constructor
  · norm_num

  unfold lowerBounds
  by_contra! h
  simp at h
  obtain ⟨ n, pos_n, binary_digits, dvd_225, n_lt ⟩ := h

  have h25 : 25 ∣ n := by omega
  have h9 : 9 ∣ n := by omega
  have hmod100 : n % 100 = 0 ∨ n % 100 = 25 ∨ n % 100 = 50 ∨ n % 100 = 75 := by
    omega

  have : 9 ∣ (Nat.digits 10 n).sum := by
    simpa [Nat.nine_dvd_iff n] using h9

  have pos_digits : 9 ≤ (Nat.digits 10 n).sum := by
    have n_ge_9 : 9 ≤ n := by
      exact Nat.le_of_dvd pos_n h9

    apply Nat.le_of_dvd ?_ this
    suffices (Nat.digits 10 n).sum ≠ 0 by
      exact Nat.zero_lt_of_ne_zero this
    intro sum_eq_0
    have : n = 0 := by
      apply Nat.digits_sum_0 (by simp : 10 ≠ 0)
      intro x x_in
      specialize binary_digits x x_in
      cases binary_digits
      · assumption
      · simp_all
        have : 1 ≤ (Nat.digits 10 (n / 10)).sum := by
          exact List.le_sum_of_mem x_in
        linarith

    linarith

  obtain ⟨ digits_le, count_eq_sum ⟩ := by
    exact digits_le binary_digits pos_digits

  have n_mod_100_zero : n % 100 = 0 := by
    have head_digit := @Nat.head!_digits 10 n (by simp : 10 ≠ 1)
    rcases hmod100 with (h | h | h | h)
    · exact h
    ·
      simp_all
      omega
    ·
      have n_mod_10 : (n / 10) % 10 = 5 := by
        omega
      have : ∀ d ∈ Nat.digits 10 (n / 10), d = 0 ∨ d = 1 := by
        intro d d_in
        specialize binary_digits d (by simp_all)
        exact binary_digits
      replace head_digit := @Nat.head!_digits 10 (n / 10) (by simp : 10 ≠ 1)
      rw [n_mod_10] at head_digit
      have pos_n_div : 0 < n / 10 := by omega
      specialize this 5 (by simp_all)
      simp_all
    ·
      simp_all
      omega

  have n_dvd_100 : 100 ∣ n := by
    exact Nat.dvd_of_mod_eq_zero n_mod_100_zero

  have digits_len_le_11 : (Nat.digits 10 n).length ≤ 11 := by
    have := Nat.digits_len 10 n (by simp) (by positivity)
    have := Nat.le_digits_len_le 10 n 11111111100 n_lt.le
    simpa using this

  have digits_len_div_le_9 :
      (Nat.digits 10 (n / 100)).length ≤ 9 := by
    have : n / 100 ≤ 111111111 := by omega
    have := Nat.le_digits_len_le 10 (n / 100) 111111111 this
    simpa using this

  have prefix_00 : (Nat.digits 10 n).take 2 = [0, 0] := by
    have n_div_mod_10 : (n / 10) % 10 = 0 := by
      omega
    have n_mod_10 : n % 10 = 0 := by
      omega
    have : ∀ d ∈ Nat.digits 10 (n / 10), d = 0 ∨ d = 1 := by
      intro d d_in
      specialize binary_digits d (by simp_all)
      exact binary_digits
    replace head_digit := @Nat.head!_digits 10 (n / 10) (by simp : 10 ≠ 1)
    have pos_n_div : 0 < n / 10 := by omega
    specialize this 0 (by simp_all)
    simp_all

  have count_ge_9 : 9 ≤ (Nat.digits 10 n).count 1 := by
    have : (List.replicate 9 1).count 1 = 9 := by rfl
    rw [<- this]
    rw [<- ge_iff_le]
    suffices Multiset.replicate 9 1 ≤ Nat.digits 10 n by
      exact List.Subperm.count_le this 1
    exact digits_le

  have count_ge_2 : 2 ≤ (Nat.digits 10 n).count 0 := by
    have pos_n_div : 0 < n / 10 := by omega
    simp_all

  have drop2_eq9 : ↑((Nat.digits 10 n).drop 2) = Multiset.replicate 9 1  := by
    have eq_append : Nat.digits 10 n = (Nat.digits 10 n).take 2 ++ (Nat.digits 10 n).drop 2 := by
      exact Eq.symm (List.take_append_drop 2 (Nat.digits 10 n))

    have card_le_card : (Multiset.replicate 9 1).card ≤ ((Nat.digits 10 n) : Multiset ℕ).card := by
      exact Multiset.card_le_card digits_le

    rw [prefix_00] at eq_append
    rw [eq_append] at digits_le card_le_card

    have le_9 : ((Nat.digits 10 n).drop 2).length ≤ 9 := by
      rw [show 11 = 9 + 2 by rfl] at digits_len_le_11
      rw [eq_append] at digits_len_le_11
      rw [List.length_append] at digits_len_le_11
      rw [show [0, 0].length = 2 by simp] at digits_len_le_11
      linarith

    have digits_le : Multiset.replicate 9 1 ≤
        ↑(List.drop 2 (Nat.digits 10 n)) := by
      have le_add : Multiset.replicate 9 1 ≤
          ({0, 0} : Multiset ℕ) + ((List.drop 2 (Nat.digits 10 n)) : Multiset ℕ) := by
        exact digits_le

      have disjoint : Disjoint ({0, 0} : Multiset ℕ) (Multiset.replicate 9 1) := by
        simp

      by_contra! h
      have : ((Nat.digits 10 n) : Multiset ℕ).sum < 9 := by
        have : ((Nat.digits 10 n) : Multiset ℕ).count 1 < 9 := by
          rw [<- Multiset.le_count_iff_replicate_le] at h
          rw [eq_append]
          simpa using h
        rwa [count_eq_sum] at this

      norm_cast at this
      omega

    have ge_9 : 9 ≤ ((Nat.digits 10 n).drop 2).length := by
      rw [show 9 = (List.replicate 9 1).length by rfl]
      exact List.Subperm.length_le digits_le

    have : ((Nat.digits 10 n).drop 2).length = 9 := by
      exact Nat.le_antisymm le_9 ge_9

    symm
    exact Multiset.eq_of_le_of_card_le digits_le le_9

  have : Nat.digits 10 n = Nat.digits 10 11111111100 := by
    rw [Eq.symm (List.take_append_drop 2 (Nat.digits 10 n))]
    rw [show Nat.digits 10 11111111100 = [0, 0] ++ List.replicate 9 1 by simp]
    rw [prefix_00]
    congr
    have repl_eq : Multiset.replicate 9 1 = ↑(List.replicate 9 1) := by
      rfl
    rw [repl_eq] at drop2_eq9
    rw [List.eq_replicate_iff]
    constructor
    · exact congrArg Multiset.card drop2_eq9
    · intro d d_in
      rw [<- repl_eq] at drop2_eq9
      rw [Multiset.eq_replicate] at drop2_eq9
      obtain ⟨ _, fa ⟩ := drop2_eq9
      exact fa d d_in

  have : n = 11111111100 := by
    apply congrArg (Nat.ofDigits 10) at this
    simp [Nat.ofDigits_digits] at this
    convert this

  simp [this] at n_lt
