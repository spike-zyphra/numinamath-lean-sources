import Mathlib
open Finset Set Nat List
noncomputable section

-- Define property: a set has infinitely many points divisible by every positive integer.
def inf_div_points (C : Set ℤ) : Prop :=
  ∀ k : ℕ+, Infinite {n ∈ C | (k : ℤ) ∣ n}

-- Prove there exists $k$ such that the set of points in $A$ divisible by $k$ is finite.
lemma exists_finite_div (A B : Set ℤ) (h_no_inf : ∀ C, (C = A ∨ C = B) → ¬ inf_div_points C) :
    ∃ k : ℕ+, Set.Finite {n ∈ A | (k : ℤ) ∣ n} := by
  by_contra! h_no_finite
  have h_inf_A : inf_div_points A := by
    intro k
    have h_inf_k : Infinite {n ∈ A | (k : ℤ) ∣ n} := by
      have h_not_finite_k : ¬Set.Finite {n ∈ A | (k : ℤ) ∣ n} := by simpa using h_no_finite k
      exact Set.infinite_coe_iff.mpr h_not_finite_k
    exact h_inf_k
  have h_contr_A := h_no_inf A (Or.inl rfl) h_inf_A
  contradiction

/-[ [Properties of numbers. General properties ]
[ Colorings $\quad]$
Each point on the number line, whose coordinate is an integer, is painted either red or blue. Prove that there is a color with the following property: for every natural number $k$ there are infinitely many points of this color, the coordinates of which are divisible by $k$.
#-/
theorem number_theory_603333 (A B : Set ℤ) (hAB : A ∪ B = univ) :
    ∃ C, (C = A ∨ C = B) ∧ inf_div_points C := by
  -- Assume no color satisfies the property (proof by contradiction).
  by_contra! h_no_color
  have h_finite_A : ∃ a : ℕ+, Set.Finite {n ∈ A | (a : ℤ) ∣ n} := by
    exact exists_finite_div A B h_no_color
  have h_finite_B : ∃ b : ℕ+, Set.Finite {n ∈ B | (b : ℤ) ∣ n} := by
    have h_no_inf_swapped : ∀ C, C = B ∨ C = A → ¬inf_div_points C := by
      intro C hC
      apply h_no_color C
      rcases hC with (rfl | rfl)
      · exact Or.inr rfl
      · exact Or.inl rfl
    exact exists_finite_div B A h_no_inf_swapped
  obtain ⟨a, h_finite_a⟩ := h_finite_A
  obtain ⟨b, h_finite_b⟩ := h_finite_B
  -- Prove the set of points in $A ∪ B$ divisible by $a * b$ is finite.
  have h_finite_union : Set.Finite {n ∈ A ∪ B | (a * b : ℤ) ∣ n} := by
    have h_finite_A_ab : Set.Finite {n ∈ A | (a * b : ℤ) ∣ n} := by
      have h_subset_A : {n ∈ A | (a * b : ℤ) ∣ n} ⊆ {n ∈ A | (a : ℤ) ∣ n} := by
        intro n hn
        simp only [mem_setOf_eq] at hn ⊢
        have h_div_a : (a : ℤ) ∣ n := by
          have h_div_ab : (a * b : ℤ) ∣ n := hn.2
          exact dvd_trans (by norm_cast; simp [Nat.dvd_mul_right]) h_div_ab
        exact ⟨hn.1, h_div_a⟩
      exact Set.Finite.subset h_finite_a h_subset_A
    have h_finite_B_ab : Set.Finite {n ∈ B | (a * b : ℤ) ∣ n} := by
      have h_subset_B : {n ∈ B | (a * b : ℤ) ∣ n} ⊆ {n ∈ B | (b : ℤ) ∣ n} := by
        intro n hn
        simp only [mem_setOf_eq] at hn ⊢
        have h_div_b : (b : ℤ) ∣ n := by
          have h_div_ab : (a * b : ℤ) ∣ n := hn.2
          exact dvd_trans (by norm_cast; simp [Nat.dvd_mul_left]) h_div_ab
        exact ⟨hn.1, h_div_b⟩
      exact Set.Finite.subset h_finite_b h_subset_B
    have h_subset_union : {n ∈ A ∪ B | (a * b : ℤ) ∣ n} ⊆ {n ∈ A | (a * b : ℤ) ∣ n} ∪ {n ∈ B | (a * b : ℤ) ∣ n} := by
      intro n hn
      simp only [mem_setOf_eq, mem_union] at hn ⊢
      have h_in_A_or_B : n ∈ A ∨ n ∈ B := by
        have h_in_union : n ∈ A ∪ B := hn.1
        exact h_in_union
      cases h_in_A_or_B with
      | inl h_in_A => exact Or.inl ⟨h_in_A, hn.2⟩
      | inr h_in_B => exact Or.inr ⟨h_in_B, hn.2⟩
    exact Set.Finite.subset (Set.finite_union.mpr ⟨h_finite_A_ab, h_finite_B_ab⟩) h_subset_union
  -- Prove the set of all integers divisible by $a * b$ is infinite.
  have h_infinite_all : Set.Infinite {n : ℤ | (a * b : ℤ) ∣ n} := by
    have h_infinite_range : Set.Infinite (range fun k : ℤ => (a * b : ℤ) * k) := by
      exact Set.infinite_range_of_injective (fun k₁ k₂ h => by simp_all [mul_right_inj'])
    have h_subset_range : range (fun k : ℤ => (a * b : ℤ) * k) ⊆ {n : ℤ | (a * b : ℤ) ∣ n} := by
      intro n hn
      rw [mem_setOf_eq]
      rcases hn with ⟨k, rfl⟩
      simp [dvd_mul_right]
    exact Set.Infinite.mono h_subset_range h_infinite_range
  have h_infinite_union : Set.Infinite {n ∈ A ∪ B | (a * b : ℤ) ∣ n} := by
    have h_subset_to_union : {n : ℤ | (a * b : ℤ) ∣ n} ⊆ {n ∈ A ∪ B | (a * b : ℤ) ∣ n} := by
      intro n hn
      have h_in_A_or_B : n ∈ A ∪ B := by
        have h_in_union : n ∈ A ∪ B := by rw [hAB]; exact mem_univ n
        exact h_in_union
      exact ⟨h_in_A_or_B, hn⟩
    exact Set.Infinite.mono h_subset_to_union h_infinite_all
  -- Contradiction: the set cannot be both finite and infinite.
  have h_finite_union' := h_finite_union
  exact h_infinite_union h_finite_union'
