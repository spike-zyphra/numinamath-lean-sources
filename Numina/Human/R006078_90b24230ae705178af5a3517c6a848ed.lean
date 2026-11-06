import Mathlib
/-Vernonia High School has 85 seniors, each of whom plays on at least one of the school's three varsity sports teams: football, baseball, and lacrosse. It so happens that 74 are on the football team; 26 are on the baseball team; 17 are on both the football and lacrosse teams; 18 are on both the baseball and football teams; and 13 are on both the baseball and lacrosse teams. Compute the number of seniors playing all three sports, given that twice this number are members of the lacrosse team.
-/

theorem combinatorics_611444 :
    -- Let F, B, and L be finite sets representing the students on each team.
    -- We can use any underlying type `α` for the students.
    ∀ (α : Type) [DecidableEq α] (F B L : Finset α),
    -- Given: The total number of students is 85.
    (F ∪ B ∪ L).card = 85 →
    -- Given: The number of students on the football team is 74.
    F.card = 74 →
    -- Given: The number of students on the baseball team is 26.
    B.card = 26 →
    -- Given: The number of students on both football and lacrosse is 17.
    (F ∩ L).card = 17 →
    -- Given: The number of students on both football and baseball is 18.
    (F ∩ B).card = 18 →
    -- Given: The number of students on both baseball and lacrosse is 13.
    (B ∩ L).card = 13 →
    -- Given: The number on the lacrosse team is twice the number on all three teams.
    L.card = 2 * (F ∩ B ∩ L).card →
    -- Goal: The number of students on all three teams is 11.
    (F ∩ B ∩ L).card = 11 := by

  intros α _ F B L h_union_card hF hB hFL hFB hBL hL_rel

 -- The Principle of Inclusion-Exclusion for three sets.
  have h_inclusion_exclusion :
      (F ∪ B ∪ L).card + (F ∩ B).card + (F ∩ L).card + (B ∩ L).card =
      F.card + B.card + L.card + (F ∩ B ∩ L).card := by
    -- State the 2-set principle for the relevant combinations of sets.
    have h1 := Finset.card_union_add_card_inter (F ∪ B) L
    have h2 := Finset.card_union_add_card_inter F B
    have h3 := Finset.card_union_add_card_inter (F ∩ L) (B ∩ L)
    rw [Finset.union_inter_distrib_right] at h1
    have h_inter_inter : (F ∩ L) ∩ (B ∩ L) = F ∩ B ∩ L := by
      ext x; simp [Finset.mem_inter, and_assoc, and_left_comm]
    rw [h_inter_inter] at h3

    linarith [h1, h2, h3]

  rw [h_union_card, hF, hB, hL_rel, hFB, hFL, hBL] at h_inclusion_exclusion

  have h_linear_eq : 85 + 18 + 17 + 13 = 74 + 26 + 2 * (F ∩ B ∩ L).card + (F ∩ B ∩ L).card := by
    exact h_inclusion_exclusion

  linarith



