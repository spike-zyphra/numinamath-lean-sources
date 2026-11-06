import Mathlib

def isPrimeSimple (n : ℕ) := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p^2 + q^2 = n

theorem number_theory_56917 :
    Set.ncard {n | n ≤ 100 ∧ isPrimeSimple n} = 6 := by
  have h1 : {n | n ≤ 100 ∧ isPrimeSimple n} = {13, 29, 34, 53, 58, 74} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume n ≤ 100 and is prime simple
      rintro ⟨hn, ⟨p, q, hp, hq, hpq, heq⟩⟩
      have h2 : p ≤ 10 := by
        by_contra h'
        push_neg at h'
        have h3 : p ^ 2 > 100 := by
          nlinarith
        nlinarith
      have h3 : q ≤ 10 := by
        by_contra h'
        push_neg at h'
        have h4 : q ^ 2 > 100 := by
          nlinarith
        nlinarith
      interval_cases p <;> interval_cases q
      <;> norm_num [Nat.Prime] at hp hq hpq heq hn ⊢
      <;> omega
    · -- Show that these are prime simple numbers
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · constructor
        · norm_num
        · refine ⟨2, 3, ?_, ?_, ?_, ?_⟩
          all_goals norm_num
      · constructor
        · norm_num
        · refine ⟨2, 5, ?_, ?_, ?_, ?_⟩
          all_goals norm_num
      · constructor
        · norm_num
        · refine ⟨3, 5, ?_, ?_, ?_, ?_⟩
          all_goals norm_num
      · constructor
        · norm_num
        · refine ⟨2, 7, ?_, ?_, ?_, ?_⟩
          all_goals norm_num
      · constructor
        · norm_num
        · refine ⟨3, 7, ?_, ?_, ?_, ?_⟩
          all_goals norm_num
      · constructor
        · norm_num
        · refine ⟨5, 7, ?_, ?_, ?_, ?_⟩
          all_goals norm_num
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]