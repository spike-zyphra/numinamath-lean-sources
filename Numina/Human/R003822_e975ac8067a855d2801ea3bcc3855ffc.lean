import Mathlib

lemma exists_two_unique : ∀ s : Finset ℕ, 2 ≤ s.card →
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ [x, y].toFinset ⊆ s := by
  intro s s_card
  have : 2 ≤ s.card := by linarith
  obtain ⟨ l, l.nodup, eq_s ⟩ := Finset.exists_list_nodup_eq s
  have : 2 ≤ l.length := by
    convert s_card
    rw [<- eq_s]
    exact Eq.symm (List.toFinset_card_of_nodup l.nodup)

  cases l with
  | nil => contradiction
  | cons x ys => cases ys with
    | nil => contradiction
    | cons y xs =>
      use x, by aesop, y, by aesop
      aesop

lemma five_subsets : ∀ s ⊆ Finset.Icc 1 50,
   s = {x ∈ s | x ≡ 0 [MOD 5]} ∪ {x ∈ s | x ≡ 1 [MOD 5] } ∪ {x ∈ s | x ≡ 2 [MOD 5] }
   ∪ {x ∈ s | x ≡ 3 [MOD 5] } ∪ {x ∈ s | x ≡ 4 [MOD 5]}
    := by
  intro s s_subset
  ext x
  mod_cases x % 5 <;> aesop

lemma mod5_unique {a n m : ℕ} (ne : n ≠ m) (h1 : a ≡ n [MOD 5])
  (n_lt : n < 5) (m_lt : m < 5) : ¬ a ≡ m [MOD 5] := by
  rw [Nat.ModEq] at *
  cases lt_or_gt_of_ne ne
    <;> omega

lemma disjoint_of_mod_diff {n m} {ne : n ≠ m} (s : Finset ℕ)
  (n_lt : n < 5) (m_lt : m < 5)  :
  Disjoint {x ∈ s | x ≡ n [MOD 5]} {x ∈ s | x ≡ m [MOD 5] } := by
  rw [Finset.disjoint_filter]
  intro x x_in x_mod_d₁ x_mod_d₂
  have := mod5_unique ne x_mod_d₁ n_lt m_lt
  rw [Nat.ModEq] at *
  exact this x_mod_d₂

lemma filter₁  : ((Finset.Icc 1 50).filter λ x => x ≡ 1 [MOD 5]).card ≤ 10 := by
  have : {x ∈ Finset.Ico 1 51 | x ≡ 1 [MOD 5]}.card = 10 := by
    have := Nat.Ico_filter_modEq_card 1 51 (r := 5) (by simp) 1
    zify
    convert this

  exact Nat.le_of_eq this

lemma filter₂  : ((Finset.Icc 1 50).filter λ x => x ≡ 2 [MOD 5]).card ≤ 10 := by
  have : {x ∈ Finset.Ico 1 51 | x ≡ 2 [MOD 5]}.card = 10 := by
    have := Nat.Ico_filter_modEq_card 1 51 (r := 5) (by simp) 2
    zify
    convert this

  exact Nat.le_of_eq this


lemma l₅part₁ : ∀ s ⊆ Finset.Icc 1 50,
  ¬(∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ x + y ≡ 0 [MOD 5]) →
  (∀ x ∈ s, x ≡ 0 [MOD 5] ∨ x ≡ 1 [MOD 5] ∨ x ≡ 2 [MOD 5]) →
    s.card < 22 := by
  intro s s_subset no_zero_pair fa

  have : {x ∈ s | x ≡ 0 [MOD 5]}.card < 2
    := by
    by_contra! gt
    apply no_zero_pair
    obtain ⟨ x, x_in, y, y_in, ne, xy_subset ⟩ :=
      exists_two_unique {x ∈ s | x ≡ 0 [MOD 5]} gt
    simp [Nat.ModEq] at *
    use x, x_in.left, y, y_in.left
    omega

  obtain ⟨ no3, no4 ⟩ : {x ∈ s | x ≡ 3 [MOD 5]} = ∅ ∧ {x ∈ s | x ≡ 4 [MOD 5]} = ∅ := by
    constructor
    all_goals
      ext x
      simp [Nat.ModEq] at *
      intro x_in c₁
      specialize fa x x_in
      rcases fa with (c₂ | c₂ | c₂)
      all_goals
        omega

  have : s = {x ∈ s | x ≡ 0 [MOD 5]} ∪
      {x ∈ s | x ≡ 1 [MOD 5] } ∪ {x ∈ s | x ≡ 2 [MOD 5] } := by
    conv_lhs =>
      rw [five_subsets s s_subset]

    simp_all

  have : s.card = {x ∈ s | x ≡ 0 [MOD 5]}.card + {x ∈ s | x ≡ 1 [MOD 5] }.card
      + {x ∈ s | x ≡ 2 [MOD 5] }.card := by
    apply congrArg Finset.card at this
    rw [<- Finset.card_union_of_disjoint
      (disjoint_of_mod_diff s (by linarith) (by linarith))
    ]
    rw [<- Finset.card_union_of_disjoint]
    · exact this
    · simp
      constructor
      all_goals apply disjoint_of_mod_diff <;> linarith
    · simp

  have : {x ∈ s | x ≡ 0 [MOD 5]}.card ≤ 10 := by
    have := Finset.filter_subset_filter (· ≡ 0 [MOD 5]) s_subset
    have : {x ∈ Finset.Icc 1 50 | x ≡ 0 [MOD 5]}.card ≤ 10 := by
      exact filter₁

    have : (( Finset.Icc 1 50).filter λ x => x ≡ 0 [MOD 5]).card ≤ 10 := by
      omega

    convert_to (s.filter λ x => x ≡ 0 [MOD 5]).card ≤
      ((Finset.Icc 1 50).filter λ x => x ≡ 0 [MOD 5]).card

    gcongr

  have : {x ∈ s | x ≡ 1 [MOD 5]}.card ≤ 10 := by
    have := Finset.filter_subset_filter (· ≡ 1 [MOD 5]) s_subset
    have : {x ∈ Finset.Icc 1 50 | x ≡ 1 [MOD 5]}.card ≤ 10 := by
      exact filter₁

    have : (( Finset.Icc 1 50).filter λ x => x ≡ 1 [MOD 5]).card ≤ 10 := by
      omega

    convert_to (s.filter λ x => x ≡ 1 [MOD 5]).card ≤
      ((Finset.Icc 1 50).filter λ x => x ≡ 1 [MOD 5]).card

    gcongr

  have : {x ∈ s | x ≡ 2 [MOD 5]}.card ≤ 10 := by
    have := Finset.filter_subset_filter (· ≡ 2 [MOD 5]) s_subset
    have : {x ∈ Finset.Icc 1 50 | x ≡ 2 [MOD 5]}.card ≤ 10 := by
      exact filter₂

    have : (( Finset.Icc 1 50).filter λ x => x ≡ 2 [MOD 5]).card ≤ 10 := by
      omega

    convert_to (s.filter λ x => x ≡ 2 [MOD 5]).card ≤
      ((Finset.Icc 1 50).filter λ x => x ≡ 2 [MOD 5]).card

    gcongr

  omega


lemma l₅part₂ : ∀ s ⊆ Finset.Icc 1 50,
  ¬(∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ x + y ≡ 0 [MOD 5]) →
  (∀ x ∈ s, x ≡ 0 [MOD 5] ∨ x ≡ 1 [MOD 5] ∨ x ≡ 3 [MOD 5]) →
    s.card < 22 := by
  intro s s_subset no_zero_pair fa

  have : {x ∈ s | x ≡ 0 [MOD 5]}.card < 2
    := by
    by_contra! gt
    apply no_zero_pair
    obtain ⟨ x, x_in, y, y_in, ne, xy_subset ⟩ :=
      exists_two_unique {x ∈ s | x ≡ 0 [MOD 5]} gt
    simp [Nat.ModEq] at *
    use x, x_in.left, y, y_in.left
    omega

  obtain ⟨ no2, no4 ⟩ : {x ∈ s | x ≡ 2 [MOD 5]} = ∅ ∧ {x ∈ s | x ≡ 4 [MOD 5]} = ∅ := by
    constructor
    all_goals
      ext x
      simp [Nat.ModEq] at *
      intro x_in c₁
      specialize fa x x_in
      rcases fa with (c₂ | c₂ | c₂)
      all_goals
        omega

  have : s = {x ∈ s | x ≡ 0 [MOD 5]} ∪
      {x ∈ s | x ≡ 1 [MOD 5] } ∪ {x ∈ s | x ≡ 3 [MOD 5] } := by
    conv_lhs =>
      rw [five_subsets s s_subset]

    simp_all

  have : s.card = {x ∈ s | x ≡ 0 [MOD 5]}.card + {x ∈ s | x ≡ 1 [MOD 5] }.card
      + {x ∈ s | x ≡ 3 [MOD 5] }.card := by
    apply congrArg Finset.card at this
    rw [<- Finset.card_union_of_disjoint
      (disjoint_of_mod_diff s (by linarith) (by linarith))
    ]
    rw [<- Finset.card_union_of_disjoint]
    · exact this
    · simp
      constructor
      all_goals apply disjoint_of_mod_diff <;> linarith
    · simp

  have : {x ∈ s | x ≡ 0 [MOD 5]}.card ≤ 10 := by
    have := Finset.filter_subset_filter (· ≡ 0 [MOD 5]) s_subset
    have : {x ∈ Finset.Icc 1 50 | x ≡ 0 [MOD 5]}.card ≤ 10 := by
      exact filter₁

    have : (( Finset.Icc 1 50).filter λ x => x ≡ 0 [MOD 5]).card ≤ 10 := by
      omega

    convert_to (s.filter λ x => x ≡ 0 [MOD 5]).card ≤
      ((Finset.Icc 1 50).filter λ x => x ≡ 0 [MOD 5]).card

    gcongr

  have : {x ∈ s | x ≡ 1 [MOD 5]}.card ≤ 10 := by
    have := Finset.filter_subset_filter (· ≡ 1 [MOD 5]) s_subset
    have : {x ∈ Finset.Icc 1 50 | x ≡ 1 [MOD 5]}.card ≤ 10 := by
      exact filter₁

    have : (( Finset.Icc 1 50).filter λ x => x ≡ 1 [MOD 5]).card ≤ 10 := by
      omega

    convert_to (s.filter λ x => x ≡ 1 [MOD 5]).card ≤
      ((Finset.Icc 1 50).filter λ x => x ≡ 1 [MOD 5]).card

    gcongr

  have : {x ∈ s | x ≡ 3 [MOD 5]}.card ≤ 10 := by
    have := Finset.filter_subset_filter (· ≡ 3 [MOD 5]) s_subset
    have : {x ∈ Finset.Icc 1 50 | x ≡ 3 [MOD 5]}.card ≤ 10 := by
      exact filter₂

    have : (( Finset.Icc 1 50).filter λ x => x ≡ 3 [MOD 5]).card ≤ 10 := by
      omega

    convert_to (s.filter λ x => x ≡ 3 [MOD 5]).card ≤
      ((Finset.Icc 1 50).filter λ x => x ≡ 3 [MOD 5]).card

    gcongr

  omega

lemma l₅part₃ : ∀ s ⊆ Finset.Icc 1 50,
  ¬(∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ x + y ≡ 0 [MOD 5]) →
  (∀ x ∈ s, x ≡ 0 [MOD 5] ∨ x ≡ 2 [MOD 5] ∨ x ≡ 4 [MOD 5]) →
    s.card < 22 := by
  intro s s_subset no_zero_pair fa

  have : {x ∈ s | x ≡ 0 [MOD 5]}.card < 2
    := by
    by_contra! gt
    apply no_zero_pair
    obtain ⟨ x, x_in, y, y_in, ne, xy_subset ⟩ :=
      exists_two_unique {x ∈ s | x ≡ 0 [MOD 5]} gt
    simp [Nat.ModEq] at *
    use x, x_in.left, y, y_in.left
    omega

  obtain ⟨ no3, no1 ⟩ : {x ∈ s | x ≡ 3 [MOD 5]} = ∅ ∧ {x ∈ s | x ≡ 1 [MOD 5]} = ∅ := by
    constructor
    all_goals
      ext x
      simp [Nat.ModEq] at *
      intro x_in c₁
      specialize fa x x_in
      rcases fa with (c₂ | c₂ | c₂)
      all_goals
        omega

  have : s = {x ∈ s | x ≡ 0 [MOD 5]} ∪
      {x ∈ s | x ≡ 2 [MOD 5] } ∪ {x ∈ s | x ≡ 4 [MOD 5] } := by
    conv_lhs =>
      rw [five_subsets s s_subset]

    simp_all

  have : s.card = {x ∈ s | x ≡ 0 [MOD 5]}.card + {x ∈ s | x ≡ 2 [MOD 5] }.card
      + {x ∈ s | x ≡ 4 [MOD 5] }.card := by
    apply congrArg Finset.card at this
    rw [<- Finset.card_union_of_disjoint
      (disjoint_of_mod_diff s (by linarith) (by linarith))
    ]
    rw [<- Finset.card_union_of_disjoint]
    · exact this
    · simp
      constructor
      all_goals apply disjoint_of_mod_diff <;> linarith
    · simp

  have : {x ∈ s | x ≡ 0 [MOD 5]}.card ≤ 10 := by
    have := Finset.filter_subset_filter (· ≡ 0 [MOD 5]) s_subset
    have : {x ∈ Finset.Icc 1 50 | x ≡ 0 [MOD 5]}.card ≤ 10 := by
      exact filter₁

    have : (( Finset.Icc 1 50).filter λ x => x ≡ 0 [MOD 5]).card ≤ 10 := by
      omega

    convert_to (s.filter λ x => x ≡ 0 [MOD 5]).card ≤
      ((Finset.Icc 1 50).filter λ x => x ≡ 0 [MOD 5]).card

    gcongr

  have : {x ∈ s | x ≡ 2 [MOD 5]}.card ≤ 10 := by
    have := Finset.filter_subset_filter (· ≡ 2 [MOD 5]) s_subset
    have : {x ∈ Finset.Icc 1 50 | x ≡ 1 [MOD 5]}.card ≤ 10 := by
      exact filter₁

    have : (( Finset.Icc 1 50).filter λ x => x ≡ 1 [MOD 5]).card ≤ 10 := by
      omega

    convert_to (s.filter λ x => x ≡ 2 [MOD 5]).card ≤
      ((Finset.Icc 1 50).filter λ x => x ≡ 2 [MOD 5]).card

    gcongr

  have : {x ∈ s | x ≡ 4 [MOD 5]}.card ≤ 10 := by
    have := Finset.filter_subset_filter (· ≡ 2 [MOD 5]) s_subset
    have : {x ∈ Finset.Icc 1 50 | x ≡ 4 [MOD 5]}.card ≤ 10 := by
      exact filter₂

    have : (( Finset.Icc 1 50).filter λ x => x ≡ 4 [MOD 5]).card ≤ 10 := by
      omega

    convert_to (s.filter λ x => x ≡ 4 [MOD 5]).card ≤
      ((Finset.Icc 1 50).filter λ x => x ≡ 4 [MOD 5]).card

    gcongr

  omega

lemma l₅part₄ : ∀ s ⊆ Finset.Icc 1 50,
  ¬(∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ x + y ≡ 0 [MOD 5]) →
  (∀ x ∈ s, x ≡ 0 [MOD 5] ∨ x ≡ 3 [MOD 5] ∨ x ≡ 4 [MOD 5]) →
    s.card < 22 := by
  intro s s_subset no_zero_pair fa

  have : {x ∈ s | x ≡ 0 [MOD 5]}.card < 2
    := by
    by_contra! gt
    apply no_zero_pair
    obtain ⟨ x, x_in, y, y_in, ne, xy_subset ⟩ :=
      exists_two_unique {x ∈ s | x ≡ 0 [MOD 5]} gt
    simp [Nat.ModEq] at *
    use x, x_in.left, y, y_in.left
    omega

  obtain ⟨ no2, no1 ⟩ : {x ∈ s | x ≡ 2 [MOD 5]} = ∅ ∧ {x ∈ s | x ≡ 1 [MOD 5]} = ∅ := by
    constructor
    all_goals
      ext x
      simp [Nat.ModEq] at *
      intro x_in c₁
      specialize fa x x_in
      rcases fa with (c₂ | c₂ | c₂)
      all_goals
        omega

  have : s = {x ∈ s | x ≡ 0 [MOD 5]} ∪
      {x ∈ s | x ≡ 3 [MOD 5] } ∪ {x ∈ s | x ≡ 4 [MOD 5] } := by
    conv_lhs =>
      rw [five_subsets s s_subset]

    simp_all

  have : s.card = {x ∈ s | x ≡ 0 [MOD 5]}.card + {x ∈ s | x ≡ 3 [MOD 5] }.card
      + {x ∈ s | x ≡ 4 [MOD 5] }.card := by
    apply congrArg Finset.card at this
    rw [<- Finset.card_union_of_disjoint
      (disjoint_of_mod_diff s (by linarith) (by linarith))
    ]
    rw [<- Finset.card_union_of_disjoint]
    · exact this
    · simp
      constructor
      all_goals apply disjoint_of_mod_diff <;> linarith
    · simp

  have : {x ∈ s | x ≡ 0 [MOD 5]}.card ≤ 10 := by
    have := Finset.filter_subset_filter (· ≡ 0 [MOD 5]) s_subset
    have : {x ∈ Finset.Icc 1 50 | x ≡ 0 [MOD 5]}.card ≤ 10 := by
      exact filter₁

    have : (( Finset.Icc 1 50).filter λ x => x ≡ 0 [MOD 5]).card ≤ 10 := by
      omega

    convert_to (s.filter λ x => x ≡ 0 [MOD 5]).card ≤
      ((Finset.Icc 1 50).filter λ x => x ≡ 0 [MOD 5]).card

    gcongr

  have : {x ∈ s | x ≡ 3 [MOD 5]}.card ≤ 10 := by
    have := Finset.filter_subset_filter (· ≡ 3 [MOD 5]) s_subset
    have : {x ∈ Finset.Icc 1 50 | x ≡ 1 [MOD 5]}.card ≤ 10 := by
      exact filter₁

    have : (( Finset.Icc 1 50).filter λ x => x ≡ 1 [MOD 5]).card ≤ 10 := by
      omega

    convert_to (s.filter λ x => x ≡ 3 [MOD 5]).card ≤
      ((Finset.Icc 1 50).filter λ x => x ≡ 3 [MOD 5]).card

    gcongr

  have : {x ∈ s | x ≡ 4 [MOD 5]}.card ≤ 10 := by
    have := Finset.filter_subset_filter (· ≡ 2 [MOD 5]) s_subset
    have : {x ∈ Finset.Icc 1 50 | x ≡ 4 [MOD 5]}.card ≤ 10 := by
      exact filter₂

    have : (( Finset.Icc 1 50).filter λ x => x ≡ 4 [MOD 5]).card ≤ 10 := by
      omega

    convert_to (s.filter λ x => x ≡ 4 [MOD 5]).card ≤
      ((Finset.Icc 1 50).filter λ x => x ≡ 4 [MOD 5]).card

    gcongr

  omega

lemma l₇ : ∀ s ⊆ Finset.Icc 1 50, 22 ≤ s.card →
  ¬(∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ x + y ≡ 0 [MOD 5]) → (
    (∀ x ∈ s, x ≡ 0 [MOD 5] ∨ x ≡ 1 [MOD 5] ∨ x ≡ 2 [MOD 5]) ∨
    (∀ x ∈ s, x ≡ 0 [MOD 5] ∨ x ≡ 1 [MOD 5] ∨ x ≡ 3 [MOD 5]) ∨
    (∀ x ∈ s, x ≡ 0 [MOD 5] ∨ x ≡ 2 [MOD 5] ∨ x ≡ 4 [MOD 5]) ∨
    (∀ x ∈ s, x ≡ 0 [MOD 5] ∨ x ≡ 3 [MOD 5] ∨ x ≡ 4 [MOD 5])
  ) := by
  simp
  intro s s_subset s_card no_zero

  have no_zero_sum : ∀ x ∈ s, ∀ x_1 ∈ s, ¬x = x_1 → x ≡ 0 [MOD 5] → ¬x_1 ≡ 0 [MOD 5] := by
    intro x x_in y y_in ne c₁ c₂
    specialize no_zero x x_in y y_in ne
    have := Nat.ModEq.add c₁ c₂
    exact no_zero this

  have x_cases : ∀ x ∈ s, x ≡ 0 [MOD 5] ∨ x ≡ 1 [MOD 5] ∨
      x ≡ 2 [MOD 5] ∨ x ≡ 3 [MOD 5] ∨ x ≡ 4 [MOD 5] := by
    intro x x_in
    conv_lhs at x_in =>
      rw [five_subsets s s_subset]

    aesop

  by_cases s1 : ∃ x ∈ s, x ≡ 1 [MOD 5]
  ·
    obtain ⟨ x, x_in, x_mod ⟩ := s1
    have : ¬∃ y ∈ s, y ≡ 4 [MOD 5] := by
      rintro ⟨ y, y_in, y_mod ⟩
      apply no_zero x x_in y y_in
      · intro eq
        subst x
        exact mod5_unique (by linarith) x_mod (by linarith) (by linarith) y_mod
      exact Nat.ModEq.add x_mod y_mod

    by_cases s2 : ∃ w ∈ s, w ≡ 2 [MOD 5]
    ·
      obtain ⟨ y, y_in, y_mod ⟩ := s2
      have : ¬∃ w ∈ s, w ≡ 3 [MOD 5] := by
        rintro ⟨ w, w_in, w_mod ⟩
        apply no_zero y y_in w w_in
        · intro eq
          subst w
          exact mod5_unique (by linarith) y_mod (by linarith) (by linarith) w_mod
        exact Nat.ModEq.add y_mod w_mod

      simp_all
    ·
      simp_all

  ·
    simp at s1
    by_cases s2 : ∃ w ∈ s, w ≡ 2 [MOD 5]
    ·
      obtain ⟨ y, y_in, y_mod ⟩ := s2
      have : ¬ ∃ w ∈ s, w ≡ 3 [MOD 5] := by
        rintro ⟨ w, w_in, w_mod ⟩
        apply no_zero y y_in w w_in
        · intro eq
          subst w
          exact mod5_unique (by linarith) y_mod (by linarith) (by linarith) w_mod
        exact Nat.ModEq.add y_mod w_mod

      simp_all
    ·
      simp_all

/-
At least 22 numbers should be taken from the natural numbers 1 to 50 to ensure
that there are two numbers whose sum is a multiple of 5.
-/
theorem number_theory_214215 : ∀ s ⊆ Finset.Icc 1 50,
  22 ≤ s.card → ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ a + b ≡ 0 [MOD 5]
    := by
  intro s s_subset s_card
  by_contra no_sum
  obtain ⟨ x, x_in, y, y_in, ne, _ ⟩ := exists_two_unique s (by linarith)
  rcases (l₇ s s_subset s_card no_sum) with (mod12 | mod13 | mod24 | mod34)
  ·
    have := l₅part₁ s s_subset no_sum mod12
    linarith
  ·
    have := l₅part₂ s s_subset no_sum mod13
    linarith
  ·
    have := l₅part₃ s s_subset no_sum mod24
    linarith
  ·
    have := l₅part₄ s s_subset no_sum mod34
    linarith
