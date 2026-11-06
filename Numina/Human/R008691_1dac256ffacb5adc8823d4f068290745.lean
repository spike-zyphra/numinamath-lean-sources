import Mathlib

/- The sequence $a_{n}$ is defined as follows: $a_{1}=56, a_{n+1}=a_{n}-1 / a_{n}$. Show that $a_{n}<0$ for some $n$ such that $0<\mathrm{n}<2002$. -/
theorem algebra_605156 (a : ℕ → ℝ) (ha1 : a 0 = 56) (han : ∀ n, a (n + 1) = a n - 1 / a n) :
    ∃ n, n < 2001 ∧ a n < 0 := by
  -- Assume on the contrary that aₙ ≥ 0 for all n < 2001.
  by_contra! h₀
  -- Show that the terms of the sequence are all rational.
  have h₁ : ∀ n, ∃ q : ℚ, a n = q := by
    intro n
    induction n with
    | zero =>
      exact ⟨56, ha1⟩
    | succ n hn =>
      obtain ⟨q, hn⟩ := hn
      rw [han, hn]
      use q - 1 / q
      norm_cast
  -- Show that the terms of the sequence never vanish.
  have h₂ : ∀ n, a n ≠ 0 := by
    -- Assume on the contrary that aₙ = 0 for some n.
    by_contra!
    obtain ⟨n, h⟩ := this
    -- Let S be the set of all n such that aₙ = 0.
    let S : Set ℕ := {n | a n = 0}
    -- Now S is nonempty.
    have hS₀ : S.Nonempty := ⟨n, h⟩
    clear n h
    -- Now S contains a minimal element, called n₀.
    let n₀ := sInf S
    have hS₁ : n₀ ∈ S := by
      exact Nat.sInf_mem hS₀
    simp [S] at hS₁
    -- Note that n₀ ≥ 2.
    have hn : n₀ ≥ 2 := by
      by_contra!
      -- If not, note that a₀ = 56 ≠ 0 and a₁ = 56 - 1 / 56 ≠ 0, contradiction.
      interval_cases n₀
      . linarith only [ha1, hS₁]
      . specialize han 0
        simp [ha1] at han
        linarith only [han, hS₁]
    -- This implies that a_{n₀ - 2} is not rational, or in other words a_{n₀ - 2} satisfies a quadratic equation with no rational root.
    obtain ⟨r, h₂⟩ := h₁ (n₀ - 2 + 1)
    have h₃ := han (n₀ - 2 + 1)
    rw [h₂, add_assoc] at h₃
    simp [hn, hS₁] at h₃
    -- Show that a_{n₀ - 1} ≠ 0, because n₀ is smallest element in S.
    have h₄ : r ≠ 0 := by
      rify
      rw [<-h₂]
      by_contra!
      replace this : n₀ - 2 + 1 ∈ S := by
        simp [S, this]
      replace this : n₀ ≤ n₀ - 2 + 1 := by
        exact Nat.sInf_le this
      omega
    field_simp at h₃
    clear h₄
    -- Show that a_{n₀ - 1} = r = ±1.
    have h₄ : (r - 1) * (r + 1) = 0 := by
      rify
      linarith only [h₃]
    simp at h₄
    -- Now consider the equation satisified by q = a_{n₀ - 2}.
    obtain ⟨q, h₅⟩ := h₁ (n₀ - 2)
    have h₆ := han (n₀ - 2)
    rw [h₂, h₅] at h₆
    -- Show that a_{n₀ - 2} ≠ 0, becuase n₀ is smallest element in S.
    have h₇ : q ≠ 0 := by
      rify
      rw [<-h₅]
      by_contra!
      replace this : n₀ - 2 ∈ S := by
        simp [S, this]
      replace this : n₀ ≤ n₀ - 2 := by
        exact Nat.sInf_le this
      omega
    field_simp at h₆
    -- In either case, we have q satisfying a quadratic equation with no rational root.
    cases h₄ with
    | inl h₄ =>
      -- If r = 1, then (2q - 1)² = 5.
      have hq : (2 * q - 1) ^ 2 = (Real.sqrt 5) ^ 2 := by
        rw [show r = 1 by linarith only [h₄]] at h₆
        rw [Real.sq_sqrt (by norm_num)]
        norm_cast at h₆ ⊢
        linarith only [h₆]
      -- This would mean √5 is rational.
      rw [sq_eq_sq_iff_abs_eq_abs, abs_of_nonneg (show 0 ≤ Real.sqrt 5 by positivity)] at hq
      have : Irrational (Real.sqrt (5 : ℕ)) := by
        rw [irrational_sqrt_natCast_iff]
        native_decide -- Decide that 5 is not a square.
      absurd this
      simp
      use |2 * q - 1|
      simp [hq]
    | inr h₄ =>
      -- If r = -1, then (2q + 1)² = 5.
      have hq : (2 * q + 1) ^ 2 = (Real.sqrt 5) ^ 2 := by
        rw [show r = -1 by linarith only [h₄]] at h₆
        rw [Real.sq_sqrt (by norm_num)]
        norm_cast at h₆ ⊢
        qify at h₆
        linarith only [h₆]
      -- This would mean √5 is rational.
      rw [sq_eq_sq_iff_abs_eq_abs, abs_of_nonneg (show 0 ≤ Real.sqrt 5 by positivity)] at hq
      have : Irrational (Real.sqrt (5 : ℕ)) := by
        rw [irrational_sqrt_natCast_iff]
        native_decide -- Decide that 5 is not a square.
      absurd this
      simp
      use |2 * q + 1|
      simp [hq]
  -- Show that the sequence is decreasing for n < 2001.
  have h₃ : ∀ n < 2001, a (n + 1) < a n := by
    intro n
    -- Prove by induction.
    induction n with
    | zero =>
      simp [han, ha1]
    | succ n hn =>
      rw [han]
      field_simp
      intro hn'
      exact lt_of_le_of_ne (h₀ (n + 1) hn') (h₂ (n + 1)).symm
  -- Rewrite the hypothesis in a more convenient form.
  replace h₃ : ∀ n, ∀ m, n + m < 2002 → a (n + m) ≤ a n := by
    intro n m
    induction m with
    | zero =>
      simp
    | succ m hm =>
      intro h
      rw [<-add_assoc]
      calc
        a (n + m + 1) ≤ a (n + m) := le_of_lt (h₃ (n + m) (by omega))
        _ ≤ a n := hm (by omega)
  -- Show that a_336 ≤ 50.
  have h₄ : a 336 ≤ 50 := by
    -- Show that a_n ≤ a_0 - n / a_0 for n ≤ 336.
    have h₄ : ∀ n ≤ 336, a n ≤ a 0 - n / a 0 := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n hn =>
        intro hn'
        calc
          a (n + 1) ≤ a n - 1 / a n := by rw [han]
          _ ≤ (a 0 - n / a 0) - 1 / a 0 := by
            apply sub_le_sub
            exact hn (by omega)
            apply div_le_div₀ (by norm_num) (by norm_num)
            exact lt_of_le_of_ne (h₀ n (by omega)) (h₂ n).symm
            specialize h₃ 0 n
            simp [show n < 2002 by omega] at h₃
            exact h₃
          _ = a 0 - (n + 1 : ℤ) / a 0 := by
            push_cast
            ring
    specialize h₄ 336 (by rfl)
    norm_num [ha1] at h₄
    exact h₄
  -- Show that a_836 ≤ 40.
  have h₅ : a 836 ≤ 40 := by
    -- Show that a_n ≤ a_336 - (n - 336) / a_336 for 336 ≤ n ≤ 836.
    have h₅ : ∀ n, 336 ≤ n ∧ n ≤ 836 → a n ≤ 50 - (n - 336) / 50 := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n hn =>
        intro hn'
        by_cases hn'' : n = 335
        . simp [hn'', h₄]
        . calc
            a (n + 1) ≤ a n - 1 / a n := by rw [han]
            _ ≤ (50 - (n - 336) / 50) - 1 / 50 := by
              apply sub_le_sub
              exact hn (by omega)
              apply div_le_div₀ (by norm_num) (by norm_num)
              exact lt_of_le_of_ne (h₀ n (by omega)) (h₂ n).symm
              specialize h₃ 336 (n - 336)
              simp [show 336 + (n - 336) < 2002 by omega] at h₃
              rw [Nat.add_sub_cancel' (by omega)] at h₃
              exact h₃.trans h₄
            _ = 50 - ((n + 1 : ℤ) - 336) / 50 := by
              push_cast
              ring
    specialize h₅ 836 ⟨by omega, by omega⟩
    norm_num [h₄] at h₅
    exact h₅
  -- Show that a_1236 ≤ 30.
  have h₆ : a 1236 ≤ 30 := by
    -- Show that a_n ≤ a_836 - (n - 836) / a_836 for 836 ≤ n ≤ 1236.
    have h₆ : ∀ n, 836 ≤ n ∧ n ≤ 1236 → a n ≤ 40 - (n - 836) / 40 := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n hn =>
        intro hn'
        by_cases hn'' : n = 835
        . simp [hn'', h₅]
        . calc
            a (n + 1) ≤ a n - 1 / a n := by rw [han]
            _ ≤ (40 - (n - 836) / 40) - 1 / 40 := by
              apply sub_le_sub
              exact hn (by omega)
              apply div_le_div₀ (by norm_num) (by norm_num)
              exact lt_of_le_of_ne (h₀ n (by omega)) (h₂ n).symm
              specialize h₃ 836 (n - 836)
              simp [show 836 + (n - 836) < 2002 by omega] at h₃
              rw [Nat.add_sub_cancel' (by omega)] at h₃
              exact h₃.trans h₅
            _ = 40 - ((n + 1 : ℤ) - 836) / 40 := by
              push_cast
              ring
    specialize h₆ 1236 ⟨by omega, by omega⟩
    norm_num [h₅] at h₆
    exact h₆
  -- Show that a_1536 ≤ 20.
  have h₇ : a 1536 ≤ 20 := by
    -- Show that a_n ≤ a_1236 - (n - 1236) / a_1236 for 1236 ≤ n ≤ 1536.
    have h₇ : ∀ n, 1236 ≤ n ∧ n ≤ 1536 → a n ≤ 30 - (n - 1236) / 30 := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n hn =>
        intro hn'
        by_cases hn'' : n = 1235
        . simp [hn'', h₆]
        . calc
            a (n + 1) ≤ a n - 1 / a n := by rw [han]
            _ ≤ (30 - (n - 1236) / 30) - 1 / 30 := by
              apply sub_le_sub
              exact hn (by omega)
              apply div_le_div₀ (by norm_num) (by norm_num)
              exact lt_of_le_of_ne (h₀ n (by omega)) (h₂ n).symm
              specialize h₃ 1236 (n - 1236)
              simp [show 1236 + (n - 1236) < 2002 by omega] at h₃
              rw [Nat.add_sub_cancel' (by omega)] at h₃
              exact h₃.trans h₆
            _ = 30 - ((n + 1 : ℤ) - 1236) / 30 := by
              push_cast
              ring
    specialize h₇ 1536 ⟨by omega, by omega⟩
    norm_num [h₆] at h₇
    exact h₇
  -- Show that a_1736 ≤ 10.
  have h₈ : a 1736 ≤ 10 := by
    -- Show that a_n ≤ a_1536 - (n - 1536) / a_1536 for 1536 ≤ n ≤ 1736.
    have h₈ : ∀ n, 1536 ≤ n ∧ n ≤ 1736 → a n ≤ 20 - (n - 1536) / 20 := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n hn =>
        intro hn'
        by_cases hn'' : n = 1535
        . simp [hn'', h₇]
        . calc
            a (n + 1) ≤ a n - 1 / a n := by rw [han]
            _ ≤ (20 - (n - 1536) / 20) - 1 / 20 := by
              apply sub_le_sub
              exact hn (by omega)
              apply div_le_div₀ (by norm_num) (by norm_num)
              exact lt_of_le_of_ne (h₀ n (by omega)) (h₂ n).symm
              specialize h₃ 1536 (n - 1536)
              simp [show 1536 + (n - 1536) < 2002 by omega] at h₃
              rw [Nat.add_sub_cancel' (by omega)] at h₃
              exact h₃.trans h₇
            _ = 20 - ((n + 1 : ℤ) - 1536) / 20 := by
              push_cast
              ring
    specialize h₈ 1736 ⟨by omega, by omega⟩
    norm_num [h₇] at h₈
    exact h₈
  -- Show that a_1836 ≤ 0.
  have h₉ : a 1836 ≤ 0 := by
    -- Show that a_n ≤ a_1736 - (n - 1736) / a_1736 for 1736 ≤ n ≤ 1836.
    have h₉ : ∀ n, 1736 ≤ n ∧ n ≤ 1836 → a n ≤ 10 - (n - 1736) / 10 := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n hn =>
        intro hn'
        by_cases hn'' : n = 1735
        . simp [hn'', h₈]
        . calc
            a (n + 1) ≤ a n - 1 / a n := by rw [han]
            _ ≤ (10 - (n - 1736) / 10) - 1 / 10 := by
              apply sub_le_sub
              exact hn (by omega)
              apply div_le_div₀ (by norm_num) (by norm_num)
              exact lt_of_le_of_ne (h₀ n (by omega)) (h₂ n).symm
              specialize h₃ 1736 (n - 1736)
              simp [show 1736 + (n - 1736) < 2002 by omega] at h₃
              rw [Nat.add_sub_cancel' (by omega)] at h₃
              exact h₃.trans h₈
            _ = 10 - ((n + 1 : ℤ) - 1736) / 10 := by
              push_cast
              ring
    specialize h₉ 1836 ⟨by omega, by omega⟩
    norm_num [h₈] at h₉
    exact h₉
  -- Show that a_1836 < 0, contradiction.
  have h₁₀ : a 1836 < 0 := by
    apply lt_of_le_of_ne h₉ (h₂ 1836)
  linarith only [h₁₀, h₀ 1836 (by norm_num)]
