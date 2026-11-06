import Mathlib

set_option linter.dupNamespace false
--set_option maxHeartbeats 800000

namespace number_theory_608375

def P n := ∃ a b c, n = 8 * a + 9 * b + 19 * c

/- This works too!
-- bounded brute-force search
instance Dec_P n : Decidable (P n) :=
  --let space := (Finset.Icc 0 n) ^ 3 -- Seems not available in Mathlib v4.15.0.
  --let Icc_0_n := Finset.Icc 0 n
  let space := (Finset.Icc 0 (n / 8)) ×ˢ (Finset.Icc 0 (n / 9)) ×ˢ (Finset.Icc 0 (n / 19))
  let n_Eq := fun (⟨a, b, c⟩ : ℕ × ℕ × ℕ) => n = 8 * a + 9 * b + 19 * c
  let solutions := space.filter n_Eq
  if whether_nonempty : solutions.Nonempty then
    isTrue (
      by
        let p := whether_nonempty.choose_spec
        set solution := whether_nonempty.choose
        have : n_Eq solution :=
          (Finset.mem_filter.mp p).2
        rcases solution with ⟨a, b, c⟩
        use a, b, c
    )
  else
    isFalse (
      by
        rintro ⟨a, b, c, n_eq⟩
        have : ⟨a, b, c⟩ ∈ solutions := by
          apply Finset.mem_filter.mpr
          constructor
          . simp [space]
            omega
          . exact n_eq
        apply whether_nonempty
        use ⟨a, b, c⟩
    )
 -/

-- bounded brute-force search
instance Dec_P n : Decidable (P n) :=
  let space := List.range (n / 8 + 1) ×ˢ List.range (n / 9 + 1) ×ˢ List.range (n / 19 + 1)
  let n_Eq : ℕ × ℕ × ℕ → Prop := fun ⟨a, b, c⟩ => n = 8 * a + 9 * b + 19 * c
  let solutions := space.filter n_Eq
  if whether_empty : solutions = [] then
    isFalse (
      by
        rintro ⟨a, b, c, n_eq⟩
        have : ⟨a, b, c⟩ ∈ solutions := by
          apply List.mem_filter.mpr
          constructor
          . simp [space]
            omega
          . convert n_eq
            simp
        have : solutions ≠ [] :=
          List.ne_nil_of_mem this
        exact this whether_empty
    )
  else
    isTrue (
      by
        let solution := solutions.head whether_empty
        have solution_in : solution ∈ solutions :=
          List.head_mem whether_empty
        have n_eq : n_Eq solution :=
          have := (List.mem_filter.mp solution_in).2
          by
            convert this
            simp
        rcases solution with ⟨a, b, c⟩
        use a, b, c
    )

-- The Houson Association of Mathematics Educators decides to hold a grand forum on mathematics education and invites a number of politicians from the United States to participate. Around lunch time the politicians decide to play a game. In this game, players can score 19 points for pegging the coordinator of the gathering with a spit ball, 9 points for downing an entire cup of the forum's interpretation of coffee, or 8 points for quoting more than three consecutive words from the speech Senator Bobbo delivered before lunch. What is the product of the two greatest scores that a player cannot score in this game?
theorem number_theory_608375 x y :
    let s := { n | ∃ a b c, n = 8 * a + 9 * b + 19 * c }ᶜ
    IsGreatest s x → IsGreatest (s \ {x}) y → x * y = 1209 := by
  intro s IsGreatest_x IsGreatest_y
  -- 1209. Attainable scores are positive integers that can be written in the form $8 a+9 b+19 c$, where $a, b$, and $c$ are nonnegative integers.
  -- Consider attainable number of points modulo 8 .
  -- Scores that are $0(\bmod 8)$ can be obtained with $8 a$ for positive $a$.
  have mod_8_eq_0_P n (n_mod_8_eq : n % 8 = 0) : P n := by
    have ⟨a, n_eq⟩ : 8 ∣ n := by omega
    use a, 0, 0
    exact n_eq
  -- Scores that are $1(\bmod 8)$ greater than or equal to 9 can be obtained with $9+8 a$ for nonnegative $a$.
  have mod_8_eq_1_P n (n_mod_8_eq : n % 8 = 1) (n_ge : n ≥ 9) : P n := by
    --have : n = n / 8 * 8 + n % 8 := (Nat.div_add_mod' n 8).symm
    let a := n / 8 - 1
    use a, 1, 0
    omega
  -- Scores that are $2(\bmod 8)$ greater than or equal to 18 can be obtained with $9 \cdot 2+8 a$.
  have mod_8_eq_2_P n (n_mod_8_eq : n % 8 = 2) (n_ge : n ≥ 18) : P n := by
    use n / 8 - 2, 2, 0
    omega
  -- Scores that are $3(\bmod 8)$ greater than or equal to 19 can be obtained with $19+8 a$.
  have mod_8_eq_3_P n (n_mod_8_eq : n % 8 = 3) (n_ge : n ≥ 19) : P n := by
    use n / 8 - 2, 0, 1
    omega
  -- Scores that are $4(\bmod 8)$ greater than or equal to $19+9=28$ can be obtained with $19+9+8 a$.
  have mod_8_eq_4_P n (n_mod_8_eq : n % 8 = 4) (n_ge : n ≥ 28) : P n := by
    use n / 8 - 3, 1, 1
    omega
  -- Scores that are $5(\bmod 8)$ greater than or equal to $19+9 \cdot 2=37$ can be obtained with $19+9 \cdot 2+8 a$.
  have mod_8_eq_5_P n (n_mod_8_eq : n % 8 = 5) (n_ge : n ≥ 37) : P n := by
    use n / 8 - 4, 2, 1
    omega
  -- Scores that are $6(\bmod 8)$ greater than or equal to $19 \cdot 2=38$ can be obtained with $19 \cdot 2+8 a$.
  have mod_8_eq_6_P n (n_mod_8_eq : n % 8 = 6) (n_ge : n ≥ 38) : P n := by
    use n / 8 - 4, 0, 2
    omega
  -- Scores that are $7(\bmod 8)$ greater than or equal to $19 \cdot 2+9=47$ can be obtained with $19 \cdot 2+9+8 a$.
  have mod_8_eq_7_P n (n_mod_8_eq : n % 8 = 7) (n_ge : n ≥ 47) : P n := by
    use n / 8 - 5, 1, 2
    omega
  have : s = Pᶜ := rfl
  let s' :=
    (Finset.range 9).filter (. % 8 = 1) ∪
    (Finset.range 18).filter (. % 8 = 2) ∪
    (Finset.range 19).filter (. % 8 = 3) ∪
    (Finset.range 28).filter (. % 8 = 4) ∪
    (Finset.range 37).filter (. % 8 = 5) ∪
    (Finset.range 38).filter (. % 8 = 6) ∪
    (Finset.range 47).filter (. % 8 = 7)
  --norm_num at s'
  have s_ss_s' : s ⊆ s' := by
    intro n n_in
    simp [s']
    set rem := n % 8
    have : rem < 8 :=
      Nat.mod_lt n (by simp)
    by_cases rem_eq : rem = 0
    . exfalso
      exact n_in (mod_8_eq_0_P n rem_eq)
    by_cases rem_eq : rem = 1
    . left
      have : n < 9 :=
        Nat.gt_of_not_le fun n_ge ↦ n_in (mod_8_eq_1_P n rem_eq n_ge)
      constructor
      . exact this
      . exact rem_eq
    right
    by_cases rem_eq : rem = 2
    . left
      constructor
      . exact Nat.gt_of_not_le fun n_ge ↦ n_in (mod_8_eq_2_P n rem_eq n_ge)
      . exact rem_eq
    right
    by_cases rem_eq : rem = 3
    . left
      constructor
      . exact Nat.gt_of_not_le fun n_ge ↦ n_in (mod_8_eq_3_P n rem_eq n_ge)
      . exact rem_eq
    right
    by_cases rem_eq : rem = 4
    . left
      constructor
      . exact Nat.gt_of_not_le fun n_ge ↦ n_in (mod_8_eq_4_P n rem_eq n_ge)
      . exact rem_eq
    right
    by_cases rem_eq : rem = 5
    . left
      constructor
      . exact Nat.gt_of_not_le fun n_ge ↦ n_in (mod_8_eq_5_P n rem_eq n_ge)
      . exact rem_eq
    right
    by_cases rem_eq : rem = 6
    . left
      constructor
      . exact Nat.gt_of_not_le fun n_ge ↦ n_in (mod_8_eq_6_P n rem_eq n_ge)
      . exact rem_eq
    right
    by_cases rem_eq : rem = 7
    . --left
      constructor
      . exact Nat.gt_of_not_le fun n_ge ↦ n_in (mod_8_eq_7_P n rem_eq n_ge)
      . exact rem_eq
    exfalso -- speeds up `omega` below
    omega
  -- copied from the result of `#eval`
  have s'_eq : s' = {1, 2, 10, 3, 11, 4, 12, 20, 5, 13, 21, 29, 6, 14, 22, 30, 7, 15, 23, 31, 39} := rfl
  --So the largest two unachievable values are 39 and 31. Multiplying them gives 1209.
  have x_eq : x = 39 := by
    have _39_in_ub : 39 ∈ upperBounds s' := by
      rw [s'_eq]
      simp
    have _39_in_s : 39 ∈ s :=
      have : ¬ P 39 := by
        decide
      this
    have ub_ss : upperBounds s' ⊆ upperBounds s :=
      upperBounds_mono_set s_ss_s'
    have : IsGreatest s 39 := by
      constructor
      . exact _39_in_s
      . --exact ub_ss _39_in_ub
        exact Set.mem_of_mem_of_subset _39_in_ub ub_ss
    exact IsGreatest.unique IsGreatest_x this
  have y_eq : y = 31 := by
    have _31_in_ub : 31 ∈ upperBounds (s' \ {x}) := by
      have s'_diff_x_eq : (s' \ {x} : Set ℕ) = {1, 2, 10, 3, 11, 4, 12, 20, 5, 13, 21, 29, 6, 14, 22, 30, 7, 15, 23, 31} := by
        rw [s'_eq, x_eq]
        exact Set.toFinset_inj.mp rfl
      rw [s'_diff_x_eq]
      simp
    have _31_in_s_diff_x : 31 ∈ s \ {x} := by
      simp
      constructor
      . have : ¬ P 31 := by
          decide
        exact this
      . simp [x_eq]
    have ub_ss : upperBounds (s' \ {x}) ⊆ upperBounds (s \ {x}) :=
      upperBounds_mono_set (Set.diff_subset_diff_left s_ss_s')
    have : IsGreatest (s \ {x}) 31 := by
      constructor
      . exact _31_in_s_diff_x
      . exact Set.mem_of_mem_of_subset _31_in_ub ub_ss
    exact IsGreatest.unique IsGreatest_y this
  simp [x_eq, y_eq]

end number_theory_608375
open number_theory_608375
