import Mathlib

/-- 30. (BUL 3) Two students $A$ and $B$ are playing the following game: Each of them writes down on a sheet of paper a positive integer and gives the sheet to the referee. The referee writes down on a blackboard two integers, one of which is the sum of the integers written by the players. After that, the referee asks student $A$ : "Can you tell the integer written by the other student?" If $A$ answers "no," the referee puts the same question to student $B$. If $B$ answers "no," the referee puts the question back to $A$, and so on. Assume that both students are intelligent and truthful. Prove that after a finite number of questions, one of the students will answer "yes." -/
theorem logic_24385 (a b x y : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hxy : x = a + b ∨ y = a + b)
    (A B : ℕ → ℤ → Set ℤ)
    (hA_0 : A 0 = fun a' ↦ {b' | 0 < b' ∧ (a' + b' = x ∨ a' + b' = y)})
    (hB_step : ∀ n, B n = fun b' ↦ {a' | 0 < a' ∧ (a' + b' = x ∨ a' + b' = y) ∧ 1 < (A n a').encard})
    (hA_step : ∀ n, A (n + 1) = fun a' ↦ {b' | 0 < b' ∧ (a' + b' = x ∨ a' + b' = y) ∧ 1 < (B n b').encard}) :
    ∃ n : ℕ, (A n a).encard ≤ 1 ∨ (B n b).encard ≤ 1 := by
  -- Let $a$ and $b$ be the integers written by $A$ and $B$ respectively, and let $x < y$ be the two integers written by the referee.
  wlog hxy' : x ≤ y generalizing x y
  · apply this y x <;> try simpa only [or_comm]
    omega
  rcases Int.le_iff_eq_or_lt.mp hxy' with hxy' | hxy'
  · use 0
    left
    simp [hA_0, hxy']
    have : {b' | 0 < b' ∧ a + b' = y} ⊆ {y - a} := by
      intro z hz
      simp at hz ⊢
      omega
    apply Set.encard_le_card at this
    simpa using this
  -- Suppose that none of $A$ and $B$ ever answers "yes".
  by_contra! h_inf
  have hA_ss (n : ℕ) (a' : ℤ) : A n a' ⊆ {b' | 0 < b' ∧ (a' + b' = x ∨ a' + b' = y)} := by
    cases n with
    | zero => simp [hA_0]
    | succ => simp [hA_step]; tauto
  have hB_ss (n : ℕ) (b' : ℤ) : B n b' ⊆ {a' | 0 < a' ∧ (a' + b' = x ∨ a' + b' = y)} := by
    simp [hB_step]; tauto
  -- We prove by induction on $n$ that $A$ at step $n$ knows that $b$ is in the interval $(n * (y - x), y - n * (y - x))$.
  have (a b : ℤ) (ha_pos : 0 < a) (hb_pos : 0 < b) (hxy : a + b = x ∨ a + b = y) (n : ℕ) : A n a ⊆ Set.Icc (n * (y - x)) (y - n * (y - x)) := by
    induction' n with n ih generalizing a b
    -- Base case: $n=0$.
    -- Initially, $A$ knows that $0 \leq b \leq y$.
    · simp [hA_0]
      intro b' hb'
      simp at hb' ⊢
      constructor
      · linarith
      have : a + b' ≤ y := by
        apply And.right at hb'
        cases hb' <;> linarith
      linarith
    -- Inductive step: $n \to n+1$.
    -- Suppose that $A$ knows that $b$ is in the interval $(n * (y - x), y - n * (y - x))$, but answers "no".
    · simp [hA_step]
      intro b' hb'
      simp at hb' ⊢
      obtain ⟨hb'_pos, hxyb', hB_encard⟩ := hb'
      have hB_ss' : B n b' = {x - b', y - b'} := by
        apply Set.Finite.eq_of_subset_of_encard_le (by simp)
        · apply (hB_ss _ _).trans
          intro z hz
          simp at hz ⊢
          omega
        · rw [Set.encard_pair]
          · convert Order.add_one_le_of_lt hB_encard
          · omega
      -- Then $B$ understands that since $A$ answered "no", both $x-a$ and $y-a$ lie in this interval.
      -- This means that $a$ is in the interval $(n * (y - x), x - n * (y - x))$.
      have hB : B n b' ⊆ Set.Icc (n * (y - x)) (x - n * (y - x)) := by
        intro a' ha'
        simp [hB_step] at ha' ⊢
        obtain ⟨ha'_pos, hxya', hA_encard⟩ := ha'
        have hA_ss' : A n a' = {x - a', y - a'} := by
          apply Set.Finite.eq_of_subset_of_encard_le (by simp)
          · apply (hA_ss _ _).trans
            intro z hz
            simp at hz ⊢
            omega
          · rw [Set.encard_pair]
            · convert Order.add_one_le_of_lt hA_encard
            · omega
        specialize ih a' b' ha'_pos hb'_pos hxya'
        have h1 : x - a' ∈ A n a' := by
          simp [hA_ss']
        have h2 : y - a' ∈ A n a' := by
          simp [hA_ss']
        apply ih at h1
        apply ih at h2
        simp at h1 h2
        omega
      -- Since $B answered "no", both $x-b$ and $y-b$ lie in this interval, which implies that $a$ is in the interval $((n + 1) * (y - x), x - (n + 1) * (y - x))$, which completes the induction.
      have h1 : x - b' ∈ B n b' := by
        simp [hB_ss']
      have h2 : y - b' ∈ B n b' := by
        simp [hB_ss']
      apply hB at h1
      apply hB at h2
      simp at h1 h2
      ring_nf at h1 h2 ⊢
      omega
  -- At each step, the interval $(n * (y - x), y - n * (y - x))$ shrinks by $2(y-x)$, so eventually it will be empty. Contradiction.
  specialize this a b ha hb (by tauto) y.natAbs
  set d := y - x
  have h_emp : Set.Icc (↑y.natAbs * d) (y - ↑y.natAbs * d) = ∅ := by
    apply Set.Icc_eq_empty_of_lt
    suffices y < 2 * y.natAbs * d by linarith
    suffices y < 2 * y.natAbs by
      have : 1 ≤ d := by simp [d]; omega
      nlinarith
    suffices y ≤ y.natAbs by omega
    exact Int.le_natAbs
  rw [h_emp] at this
  simp at this
  specialize h_inf y.natAbs
  simp [this] at h_inf
