import Mathlib

abbrev Condition n := 17 ∣ (Nat.digits 10 n).sum ∧ 17 ∣ (Nat.digits 10 (n + 1)).sum

lemma condition_met_by_8899 : ∃ x, Condition x := ⟨8899, by unfold Condition; norm_num⟩

-- We ask lean to automatically handle cases for n < 8899, but not with `interval_cases n`;
-- wo use a native function to **compute** the minimum with a proof!
lemma minimum_is_8899 : Nat.find (p := Condition) condition_met_by_8899 = 8899 := by native_decide

/- Preparing for the club lesson, the children found such 2 natural consecutive numbers,
  the smallest of the possible ones, that the sum of the digits of each of them is
  divisible by 17. What numbers did the children find? -/
theorem number_theory_233364 :
  IsLeast {n | 17 ∣ (Nat.digits 10 n).sum ∧ 17 ∣ (Nat.digits 10 (n + 1)).sum} 8899 := by
  constructor
  · constructor
    · norm_num
    · norm_num
  · intro n hn
    rcases hn with ⟨h1, h2⟩
    by_contra h
    simp at h
    have := Nat.find_min' condition_met_by_8899 (m := n) (by tauto)
    rw [minimum_is_8899] at this
    omega
