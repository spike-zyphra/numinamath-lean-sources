import Mathlib

-- the inductive definition that a state is reachable from the start state
-- `valid_start` here is condition on possible start states, that they have to satisfy
-- `valid_step` is condition on two states,
-- if it is fulfilled then the change from the first to the second is allowed
inductive reachable_state {A} {valid_start: A → Prop} {valid_step: A → A → Prop} (start: A): A → Prop where
| start: valid_start start → reachable_state start start
| step: ∀ (before after: A), reachable_state start before → valid_step before after → reachable_state start after

-- an inequality that the proof below uses
lemma inequality {a b: ℝ} (Ha: 0 < a) (Hb: 0 < b): 4 / (a + b) ≤ 1 / a + 1 / b := by
  have H1: a ≠ 0 := Ne.symm (ne_of_lt Ha)
  have H2: b ≠ 0 := Ne.symm (ne_of_lt Hb)
  have H3: 0 < a + b := by linarith
  have H4: 0 < a * b := mul_pos Ha Hb
  field_simp
  have H6: 4 * a * b ≤ (a + b) ^ 2 := four_mul_le_pow_two_add a b
  have H7: 0 < a * b * (a + b) := mul_pos H4 H3
  have H8: 4 * a * b / ((a * b) * (a + b)) ≤ (a + b) ^ 2 / ((a * b) * (a + b)) :=
    (div_le_div_iff_of_pos_right H7).mpr H6
  have H9: 4 * a * b / (a * b * (a + b)) = 4 / (a + b) := by
    field_simp
    ring
  have H10: (a + b) ^ 2 / (a * b * (a + b)) = (b + a) / (a * b) := by
    field_simp
    ring
  rw [H9, H10] at H8
  exact H8

-- a tiny lemma, used only in the proof of the following lemma `lemma_2`
lemma lemma_1 {s: Multiset ℝ} {x: ℝ} (H: x ∈ s):
    (s.erase x) + {x} = s := by
  rw [Multiset.add_singleton_eq_iff]
  simp_all

-- a lemma about an effect that the erasing an element from multiset
-- has on its sum (if the element is contained in the multiset)
lemma lemma_2 {s: Multiset ℝ} {x: ℝ} (H: x ∈ s):
    (s.erase x).sum = s.sum - x := by
  have H0 := lemma_1 H
  apply_fun Multiset.sum at H0
  simp at H0
  linarith


/- [Example 4.6.6] There are $n$ real numbers written on the blackboard. Any two numbers are erased, for example, $a$ and $b$, and a new number $\frac{a+b}{4}$ is written, thus reducing the number of numbers on the blackboard by one each time. After performing this operation $n-1$ times, only one number remains on the blackboard.

Prove: If initially, the blackboard has $n$ ones, then regardless of the order in which the $n-1$ operations are performed, the number left on the blackboard is certainly no less than $\frac{1}{n}$. -/
theorem algebra_225556 {n : ℕ} (hn : 0 < n)
    (start_state end_state: Multiset ℝ) (H: start_state = Multiset.replicate n 1) (H0: end_state.card = 1)
    (valid_step: Multiset ℝ → Multiset ℝ → Prop)
    (H1: ∀ before after, valid_step before after =
         ∃ (x y: ℝ), (if x = y then 2 ≤ before.count x else x ∈ before ∧ y ∈ before) ∧
         after = ((before.erase x).erase y).cons ((x + y) / 4))
    (H2: @reachable_state _ (fun _ => True) valid_step start_state end_state):
    ∃ last_number, end_state = {last_number} ∧ 1 / (n: ℝ) ≤ last_number := by

  -- a predicate on multiset, which says that all of its values is positive
  set all_positive: Multiset ℝ → Prop := fun s => ∀ a ∈ s, 0 < a

  -- this lemma states, that states/multisets that are with all values positive,
  -- stays such after any valid change or step
  have all_positive_move_invariant {before after: Multiset ℝ} (H3: valid_step before after) (H4: all_positive before):
      all_positive after := by
    -- let use the definition of `valid_step`
    rw [H1] at H3
    -- and then use all the information we obtained
    obtain ⟨x, y, H5, H6⟩ := H3
    -- let's split the `if` in the `H5`
    split_ifs at H5 <;> rename_i H7
    . -- substitute value of `y` and also multiset `after` everywhere
      subst y after
      -- unfold the definition of the condition `all_positive` and simplify
      unfold all_positive
      simp
      constructor
      . -- the first part of the goal:
        -- `x` is contained in the multiset `before`,
        -- because it's count in this multiset is at least `2`
        have H8: x ∈ before := Multiset.count_pos.mp (by linarith)
        exact H4 x H8
      . -- the second part of the goal:
        -- `x` is contained in the multiset `befoere` even after
        -- the value `x` is removed from it once
        intros a Ha
        have H8: a ∈ before.erase x := Multiset.mem_of_mem_erase Ha
        have H9: a ∈ before := Multiset.mem_of_mem_erase H8
        exact H4 a H9
    . -- substitue value of multiset `after` everywhere
      subst after
      -- unfold the definition of the condition `all_positive` and simplify
      unfold all_positive
      simp
      constructor
      . -- the first part of goal is easy
        exact Right.add_pos' (H4 x H5.1) (H4 y H5.2)
      . intros a Ha
        -- if `a` is contained in the multiset `before`
        -- even after a value is removed from it twice
        -- then it is contained in original `before` too
        have H8: a ∈ before.erase x := Multiset.mem_of_mem_erase Ha
        have H9: a ∈ before := Multiset.mem_of_mem_erase H8
        exact H4 a H9

  -- now we prove that for any start state, that has all of it values positive,
  -- any reachable state also has this property.
  -- proof is easy, using iduction on inductive predicate `reachable_state`
  have all_positive_game_invariant (start: Multiset ℝ) (H3: all_positive start):
      ∀ (state: Multiset ℝ), @reachable_state _ (fun _ => True) valid_step start state → all_positive state := by
    intros state H4
    induction H4 with
    | start _ => exact H3
    | step before after iH iH0 iH1 =>
      apply all_positive_move_invariant iH0 iH1

  -- we define an abbreviature `f` for the sum of reciprocal values of multiset elements
  set f: Multiset ℝ → ℝ := fun s => (s.map (fun x => 1 / x)).sum

  -- value of `f` is not increasing after any possible move.
  -- if the state before move had all it's values positive and
  -- it is valid change
  have f_not_increasing_move_invariant {before after: Multiset ℝ}
      (H3: valid_step before after) (H4: all_positive before):
      f after ≤ f before := by
    -- let's unfold the definiton of `f`
    -- and replace the `valid_step`in the `H3` using the `H1`
    -- then use the obtained information
    unfold f
    rw [H1] at H3
    obtain ⟨x, y, H5, H6⟩ := H3
    -- let's split the `if` in the hypothesis `H5`
    split_ifs at H5 <;> rename_i H7
    . -- substitute values of the `y` and `after` everywhere
      subst y after
      -- useful simplications
      simp only [Multiset.map_cons, Multiset.sum_cons]
      field_simp
      -- we need these facts about `x` and its membership
      -- in the multiset `before` (originally and even aftter removing `x` once)
      have H6: x ∈ before := Multiset.count_pos.mp (by linarith)
      have H7: x ∈ before.erase x := Multiset.count_pos.mp (by simp; linarith)
      -- some library lemmas to prepare for use of `lemma_2`
      rw [Multiset.map_erase_of_mem _ _ H7, Multiset.map_erase_of_mem _ _ H6]
      rw [lemma_2, lemma_2]
      . -- we know that `a` is positive, because it belongs to multiset `before`
        -- which has all of its values positive
        apply H4 at H6
        -- finally we use `linarith` with an hint to solve this goal
        linarith [inequality H6 H6]
      . -- first of two results we need to prove because we used `lemma_2` twice
        exact Multiset.mem_map_of_mem (fun x => 1 / x) H6
      . -- second of the two results
        rw [<- Multiset.map_erase_of_mem _ _ H6]
        exact Multiset.mem_map_of_mem (fun x => 1 / x) H7
    . -- substitute value of `after` everywhere and simplify a bit
      subst after
      simp only [Multiset.map_cons, Multiset.sum_cons]
      -- `y` is in the multiset even after removing `x` from it once,
      -- because `x` and `y` is not equal
      have H8: y ∈ before.erase x :=
        (Multiset.mem_erase_of_ne (by exact fun a => H7 a.symm)).mpr H5.2
      -- prepare the goal for the use of `lemma_2`
      rw [Multiset.map_erase_of_mem _ _ H8, Multiset.map_erase_of_mem _ _ H5.1]
      rw [lemma_2, lemma_2]
      . -- some simplification
        field_simp
        -- let's use an information in `H5`
        obtain ⟨H9, H10⟩ := H5
        -- both `x` and `y` are positive, beecause they are in multiset `before`
        -- which has values in it positive
        apply H4 at H9
        apply H4 at H10
        linarith [inequality H9 H10]
      . exact Multiset.mem_map_of_mem (fun x => 1 / x) H5.1
      . rw [<- Multiset.map_erase_of_mem _ _ H5.1]
        exact Multiset.mem_map_of_mem (fun x => 1 / x) H8

  -- now we prove that for any start state with all values positive
  -- any reachable state's value of `f` is less or equal to the value of `f` of start state.
  -- proof by induction on the fact that a state is reachable
  have f_not_increasing_game_invariant (start: Multiset ℝ) (H3: all_positive start):
      ∀ (state: Multiset ℝ), @reachable_state _ (fun _ => True) valid_step start state →
      f state ≤ f start := by
    intros state H4
    induction H4 with
    | start _ => simp
    | step before after iH iH0 iH1 =>
      -- helpful inequality to prepare for the use of transitivity
      have H4: f after ≤ f before :=
        f_not_increasing_move_invariant iH0 (all_positive_game_invariant start H3 before iH)
      -- we use the fact that relation `≤` is transitive
      exact Preorder.le_trans (f after) (f before) (f start) H4 iH1

  -- we prove that the given start state is with values in it, that are all positive
  have start_state_all_positive: all_positive start_state := by
    simp [H, all_positive]
    intros a Ha
    rw [@Multiset.mem_replicate] at Ha
    linarith

  -- two helpful results:
  -- 1) end state has value of `f` less or equal to the start state
  -- 2) end state has all values in it positive
  have H3 := f_not_increasing_game_invariant start_state start_state_all_positive end_state H2
  have H5: all_positive end_state :=
    all_positive_game_invariant start_state start_state_all_positive end_state H2

  -- the end state has only one value in it
  -- therefore there is such `a` that end state is equal to `{a}`.
  -- we use this information and substitue end state everywhere with `{a}`
  rw [Multiset.card_eq_one] at H0
  obtain ⟨a, H0⟩ := H0
  subst H0

  -- some simplication
  simp only [Multiset.singleton_inj, exists_eq_left', ge_iff_le]

  -- we prove that the value of `f` of the start state is equal to `n`
  have H4: f start_state = (n: ℝ) := by
    simp [f, H]

  -- after a rewrite and some simplification we reach the final step of the proof
  rw [H4] at H3
  simp only [Multiset.map_singleton, Multiset.sum_singleton, f] at H3

  -- for the proof to work, we we will prove that `0 < a` and `0 < n`, too
  have H6: 0 < a := by
    simp only [Multiset.mem_singleton, forall_eq, all_positive] at H5
    exact H5
  have H7: 0 < (n: ℝ) := by norm_cast

  -- final step
  have H8: 1 ≤ (n: ℝ) * a := (mul_inv_le_iff₀ H6).mp H3
  exact (one_div_le H6 H7).mp H3