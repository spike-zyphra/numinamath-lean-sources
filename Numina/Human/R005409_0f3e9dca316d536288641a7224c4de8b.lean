import Mathlib

def next_num (n : ℕ) := Finset.Icc (2 * n) (3 * n)

mutual

inductive WinningNum : ℕ → Prop where
| next_lose (h1 : n < 2007) (h : ∀ x ∈ next_num n, LosingNum x) : WinningNum n

inductive LosingNum : ℕ → Prop where
| lose (h : 2007 ≤ n) : LosingNum n
| next_win (y : ℕ) (hy : y ∈ next_num n) (h : WinningNum y) : LosingNum n

end

open WinningNum LosingNum

lemma lemma_lose_cant_win : n ≠ 0 → LosingNum n → ¬WinningNum n := by
  induction n using Nat.strong_decreasing_induction
  case base =>
    use 2007
    intro m hm hne hlose hwin
    obtain ⟨h1, h2⟩ := hwin
    linarith
  case step n ih =>
    intro hne hlose hwin
    obtain ⟨h1, h2⟩ := hwin
    match hlose with
    | lose h => linarith
    | next_win y hy h =>
        specialize h2 y hy
        simp [next_num] at hy
        specialize ih y (by omega) (by omega)
        tauto

theorem logic_and_puzzles_608175 :
  { n ≠ 0 | n < 10 ∧ WinningNum n }.ncard = 6 := by
  -- I win if I say any number between 1004 and 2006.
  have win_1004_to_2006 : ∀ d ∈ Finset.Icc 1004 2006, WinningNum d := by
    intro d hd
    simp at hd
    apply next_lose (by omega)
    intro x hx
    simp [next_num] at hx
    apply lose
    omega
  -- Thus, by saying such a number, my friend can force a win for himself if I ever say a number between 335 and 1003.
  have lose_335_to_1003 : ∀ d ∈ Finset.Icc 335 1003, LosingNum d := by
    intro d hd
    simp at hd
    apply next_win (max 1004 (2 * d))
    . simp [next_num]
      omega
    . apply win_1004_to_2006
      simp
      omega
  --  Then I win if I say any number between 168 and 334 , because my friend must then say one of the losing numbers just considered.
  have win_168_to_334 : ∀ d ∈ Finset.Icc 168 334, WinningNum d := by
    intro d hd
    simp at hd
    apply next_lose (by omega)
    intro x hx
    simp [next_num] at hx
    apply lose_335_to_1003
    simp
    omega
  -- Similarly, I lose by saying 56 through 167
  have lose_56_to_167 : ∀ d ∈ Finset.Icc 56 167, LosingNum d := by
    intro d hd
    simp at hd
    apply next_win (max 168 (2 * d))
    . simp [next_num]
      omega
    . apply win_168_to_334
      simp
      omega
  -- win by saying 28 through 55
  have win_28_to_55 : ∀ d ∈ Finset.Icc 28 55, WinningNum d := by
    intro d hd
    simp at hd
    apply next_lose (by omega)
    intro x hx
    simp [next_num] at hx
    apply lose_56_to_167
    simp
    omega
  -- lose with 10 through 27
  have lose_10_to_17 : ∀ d ∈ Finset.Icc 10 27, LosingNum d := by
    intro d hd
    simp at hd
    apply next_win (max 28 (2 * d))
    . simp [next_num]
      omega
    . apply win_28_to_55
      simp
      omega
  -- win with 5 through 9
  have win_5_to_9 : ∀ d ∈ Finset.Icc 5 9, WinningNum d := by
    intro d hd
    simp at hd
    apply next_lose (by omega)
    intro x hx
    simp [next_num] at hx
    apply lose_10_to_17
    simp
    omega
  -- lose with 2 through 4
  have lose_2_to_4 : ∀ d ∈ Finset.Icc 2 4, LosingNum d := by
    intro d hd
    simp at hd
    apply next_win (max 5 (2 * d))
    . simp [next_num]
      omega
    . apply win_5_to_9
      simp
      omega
  -- and win with 1.
  have win_1 : WinningNum 1 := by
    apply next_lose (by omega)
    intro x hx
    simp [next_num] at hx
    apply lose_2_to_4
    simp
    omega
  suffices {n ≠ 0 | n < 10 ∧ WinningNum n} = {1, 5, 6, 7, 8, 9} by
    rw [this]
    simp [Set.ncard, Set.encard]
  ext n
  constructor
  . intro h
    simp at h
    obtain ⟨h1, h2, h3⟩ := h
    simp
    interval_cases h : n
    case «0» => contradiction
    case «2» | «3» | «4» =>
      specialize lose_2_to_4 n (by subst n; simp)
      subst n
      apply lemma_lose_cant_win (by simp) at lose_2_to_4
      contradiction
    all_goals
    omega
  . intro h
    simp at h
    by_cases n = 1
    . simp
      subst n
      iterate 2 constructor; omega
      assumption
    . specialize win_5_to_9 n (by simp; omega)
      simp
      iterate 2 constructor; omega
      assumption
