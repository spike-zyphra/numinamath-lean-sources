import Mathlib

/-
PROBLEM: Mary told John her score on the American
High School Mathematics Examination (AHSME), which
was over 80. From this, John was able to determine
the number of problems Mary solved correctly. If
Mary's score had been any lower, but still over 80,
John could not have determined this. What was Mary's
score? (Recall that the AHSME consists of 30
multiple choice problems and that one's score, s, is
computed by the formula s=30+4c−w, where c is the
number of correct answers and w is the number of
wrong answers. (Students are not penalized for
problems left unanswered.)
-/

theorem logic_and_puzzles_94526 :
IsLeast {s : ℕ | ∃! (x : ℕ×ℕ), x.1 ≤ 30 ∧ x.2 ≤ 30 - x.1 ∧ 80 < s ∧ s = 30 + 4*x.1 - x.2} 119 := by {
  constructor
  -- Show that 119 satisfies the set conditions
  simp
  constructor
  swap
  use 23
  use 3
  constructor
  norm_num
  intro ⟨a,b⟩
  simp
  intros ha hb hab
  -- If a is < 23 then 30 + 4*a - b < 119.
  have : a ≥ 23 := by {
    apply le_of_eq at hab
    contrapose hab
    apply Nat.not_le_of_gt
    apply Nat.lt_of_not_ge at hab
    calc 30 + 4*a - b ≤ 30 + 4*a := by norm_num
      _ < 119 := by linarith
  }
  -- If a > 23 then for 119 = 30 + 4*a - b to work,
  -- we must have b > 30 - a, a contradiction
  have hale23 : a ≤ 23 := by {
    apply ge_of_eq at hab
    contrapose hab
    apply Nat.not_le_of_gt
    apply Nat.lt_of_not_ge at hab
    rw [Nat.lt_iff_add_one_le] at hab
    norm_num at hab
    rw [gt_iff_lt]
    have hblt7 : b < 7 := by {
      calc b ≤ 30 - a := by exact hb
        _ < 30 - 23 := by {apply Nat.sub_lt_sub_left; trivial; linarith}
        _ = 7 := by norm_num
    }
    calc 119 = 126 - 7 := by norm_num
      _ < 126 - b := by {apply Nat.sub_lt_sub_left; linarith; exact hblt7}
      _ = 30 + 4*24 - b := by norm_num
      _ ≤ 30 + 4*a - b := by {rw [Nat.sub_le_sub_iff_right]; linarith; linarith}
  }
  have ha23 : a = 23 := by rw [Nat.eq_iff_le_and_ge]; exact ⟨hale23,this⟩
  constructor
  exact ha23
  rw [ha23] at hab
  simp at hab
  symm at hab
  rw [Nat.sub_eq_iff_eq_add (by {apply le_trans hb; rw [ha23]; trivial}),
      add_comm,
      ←Nat.sub_eq_iff_eq_add (by trivial)] at hab
  simp at hab
  exact hab.symm

  -- This concludes the proof that 119 satisfies the
  -- conditions. Now we show that any number that
  -- satisfies the condition has to be ≥ 119. We
  -- do this by contradiction, assuming it was < 119.

  rw [mem_lowerBounds]
  intro s
  simp
  intro h1
  rcases h1 with ⟨x,h1⟩
  simp at h1
  rcases h1 with ⟨⟨ha,hb,hs,hseq⟩,h2⟩
  contrapose h2
  simp
  simp at h2
  -- an auxiliary statement that will be used throughout
  have hx1x2 : x.2 ≤ 4*x.1 := by {
    by_contra hx1x2
    simp at hx1x2
    suffices : 80 < 30
    linarith
    calc 80 < s := by exact hs
      _ = 30 + 4*x.1 - x.2 := by rw [hseq]
      _ ≤ 30 + x.2 - x.2 := by {
        apply Nat.le_of_lt at hx1x2
        apply Nat.sub_le_sub_right
        apply Nat.add_le_add_left
        exact hx1x2
      }
      _ ≤ 30 := by norm_num
  }

  /- We do a case distinction according to whether
  (b = ) x.2 ≥ 4 or not. If it is, we show that
  x is not unique by showing that (x.1-1,x.2-4)
  also satisfies all the conditions. Otherwise,
  we show that (x.1+1,x.2+4) does. This will
  eventually give the claim.
  -/
  by_cases hx2ge4 : x.2 ≥ 4
  use x.1 - 1
  constructor
  simp
  linarith

  use x.2 - 4
  constructor
  simp
  rw [←Nat.sub_add_comm]
  simp
  calc x.2 ≤ 30 - x.1 := by exact hb
    _ = 30 - 1 - (x.1 - 1) := by {
      rw [Nat.sub_sub_sub_cancel_right]
      by_contra hx10
      simp at hx10
      rw [hx10] at hseq
      simp at hseq
      rw [hseq] at hs
      suffices : 80 < 30
      trivial
      calc 80 < 30 - x.2 := by exact hs
        _ ≤ 30 := by norm_num
    }
    _ ≤ 34 - (x.1 - 1) := by simp; rw [Nat.sub_add_eq_max]; norm_num

  by_contra hx1
  simp at hx1
  have : x.1 = 30 := by linarith
  rw [this] at hb
  simp at hb
  linarith
  constructor
  exact hs
  constructor
  rw [hseq, Nat.mul_sub]
  simp
  symm
  rw [Nat.add_sub_assoc, Nat.sub_sub_sub_cancel_right, Nat.add_sub_assoc]
  exact hx1x2

  trivial
  apply Nat.sub_le_sub_right
  exact hx1x2
  by_contra heq
  have hsubself : x.2 - 4 = x.2 := congr_arg (λ (x : ℕ×ℕ) ↦ x.2) heq
  have : x.2 = x.2 + 4 := by {
    apply (Nat.sub_eq_iff_eq_add _).1
    exact hsubself
    rw [ge_iff_le] at hx2ge4
    exact hx2ge4
  }
  linarith
  simp at hx2ge4
  use x.1 + 1
  constructor
  by_contra hxp1
  simp at hxp1
  have : x.1 = 30 := by linarith
  rw [this] at hseq
  simp at hseq
  suffices : 146 < 119
  trivial
  calc 146 = 150 - 4 := by trivial
    _ < 150 - x.2 := by {apply Nat.sub_lt_sub_left; linarith; exact hx2ge4}
    _ = s := by rw [←hseq]
    _ < 119 := by exact h2
  
  use x.2 + 4
  constructor
  simp
  suffices : x.1 ≤ 22
  calc x.2 + 4 ≤ 7 := by {
    apply Nat.lt_iff_add_one_le.1 at hx2ge4
    linarith
  }
    _ ≤ 29 - x.1 := by {
      apply (Nat.le_sub_iff_add_le _).2
      linarith
      by_contra hx1
      simp at hx1
      have : x.1 = 30 := by linarith
      rw [this] at hseq
      rw [hseq] at h2
      simp at h2
      linarith
    }
  
  by_contra hx1
  simp at hx1
  rw [Nat.lt_iff_add_one_le] at hx1
  simp at hx1
  suffices : 119 < 119
  linarith
  calc 119 = 30 + 4*23 - 3 := by trivial
    _ ≤ 30 + 4*23 - x.2 := by {apply Nat.sub_le_sub_left; linarith}
    _ ≤ 30 + 4*x.1 - x.2 := by {apply Nat.sub_le_sub_right; apply Nat.add_le_add_left; linarith}
    _ = s := by rw [←hseq]
    _ < 119 := by exact h2
  
  constructor
  exact hs
  constructor
  rw [hseq, Nat.mul_add, Nat.mul_one]
  symm
  rw [Nat.add_sub_assoc, Nat.add_sub_add_right, ←Nat.add_sub_assoc]
  exact hx1x2
  linarith
  by_contra heq
  have haddself : x.2 + 4 = x.2 := congr_arg (λ (x : ℕ×ℕ) ↦ x.2) heq
  linarith
}