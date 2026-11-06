import Mathlib

theorem number_theory_279799 (G : Finset ℕ) (hG : G = {3, 4, 5, 6, 7, 8, 9}) :
    (Nat.card {x | x ∈ G ∧ Nat.Prime x}) * 4 = (Nat.card {x | x ∈ G ∧ ¬Nat.Prime x}) * 3 := by
  rw [hG]
  have h1 : Nat.card {x | x ∈ ({3, 4, 5, 6, 7, 8, 9} : Finset ℕ) ∧ Nat.Prime x} = 3 := by
    have h2 : {x | x ∈ ({3, 4, 5, 6, 7, 8, 9} : Finset ℕ) ∧ Nat.Prime x} = {3, 5, 7} := by
      ext n
      simp
      constructor
      · -- Assume n in the left side
        intro h
        rcases h with ⟨h1, h2⟩
        have h3 : n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by
          omega
        rcases h3 with (r | r | r | r | r | r | r)
        · -- n = 3
          rw [r]
          all_goals tauto
        · -- n = 4
          exfalso
          rw [r] at h2
          norm_num at h2
        · -- n = 5
          rw [r]
          all_goals tauto
        · -- n = 6
          exfalso
          rw [r] at h2
          norm_num at h2
        · -- n = 7
          rw [r]
          all_goals tauto
        · -- n = 8
          exfalso
          rw [r] at h2
          norm_num at h2
        · -- n = 9
          exfalso
          rw [r] at h2
          norm_num at h2
      · -- Assume n in the right side
        rintro (r | r | r)
        · -- n = 3
          rw [r]
          all_goals constructor <;> norm_num
        · -- n = 5
          rw [r]
          all_goals constructor <;> norm_num
        · -- n = 7
          rw [r]
          all_goals constructor <;> norm_num
    rw [h2]
    norm_num
  have h3 : Nat.card {x | x ∈ ({3, 4, 5, 6, 7, 8, 9} : Finset ℕ) ∧ ¬Nat.Prime x} = 4 := by
    have h4 : {x | x ∈ ({3, 4, 5, 6, 7, 8, 9} : Finset ℕ) ∧ ¬Nat.Prime x} = {4, 6, 8, 9} := by
      ext n
      simp
      constructor
      · -- Assume n in the left side
        intro h
        rcases h with ⟨h1, h2⟩
        have h3 : n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by
          omega
        rcases h3 with (r | r | r | r | r | r | r)
        · -- n = 3
          rw [r] at h2
          norm_num at h2
        · -- n = 4
          rw [r]
          all_goals tauto
        · -- n = 5
          rw [r] at h2
          norm_num at h2
        · -- n = 6
          rw [r]
          all_goals tauto
        · -- n = 7
          rw [r] at h2
          norm_num at h2
        · -- n = 8
          rw [r]
          all_goals tauto
        · -- n = 9
          rw [r]
          all_goals tauto
      · -- Assume n in the right side
        rintro (r | r | r | r)
        · -- n = 4
          rw [r]
          all_goals constructor <;> norm_num
        · -- n = 6
          rw [r]
          all_goals constructor <;> norm_num
        · -- n = 8
          rw [r]
          all_goals constructor <;> norm_num
        · -- n = 9
          rw [r]
          all_goals constructor <;> norm_num
    rw [h4]
    norm_num
  calc
    (Nat.card {x | x ∈ ({3, 4, 5, 6, 7, 8, 9} : Finset ℕ) ∧ Nat.Prime x}) * 4 = 3 * 4 := by
      rw [h1]
    _ = 4 * 3 := by
      norm_num
    _ = (Nat.card {x | x ∈ ({3, 4, 5, 6, 7, 8, 9} : Finset ℕ) ∧ ¬Nat.Prime x}) * 3 := by
      rw [h3]