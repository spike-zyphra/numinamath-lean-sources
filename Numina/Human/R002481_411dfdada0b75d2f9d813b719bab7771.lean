import Mathlib

open Nat Finset

/-- Using the digits 1, 2, 3, 4, 5, 6, 7, and 9, form 4 two-digit prime numbers, using each digit
only once. What is the sum of the 4 prime numbers?

$\text{(A)}\ 150 \qquad \text{(B)}\ 160 \qquad \text{(C)}\ 170 \qquad \text{(D)}\ 180 \qquad
\text{(E)}\ 190$ -/
theorem number_theory_94013 (d : ℕ → ℕ → ℕ) (hd1 : ∀ i j, (d i j) ∈ ({1, 2, 3, 4, 5, 6, 7, 9} : Set ℕ))
    (hd2 : ∀ i1 ∈ range 4, ∀ j1 ∈ range 2, ∀ i2 ∈ range 4, ∀ j2 ∈ range 2, d i1 j1 = d i2 j2 → i1 = i2 ∧ j1 = j2)
    (p : ℕ → ℕ) (hp1 : ∀ i, digits 10 (p i) = [d i 0, d i 1]) (hp : ∀ i, (p i).Prime) :
    ∑ i ∈ range 4, p i = 190 := by

  -- Let $p_0, p_1, p_2, p_3$ be the prime numbers. Write $p_i = 10d_{i,1} + d_{i,0}$.
  have p_i_eq_add_ten_mul (i) : p i = d i 0 + 10 * d i 1 := by
    apply_fun digits 10
    on_goal 2 => exact digits.injective 10
    rw [hp1, Nat.digits_add 10 (by norm_num), Nat.digits_of_lt]
    all_goals {
      have := hd1 i 0; simp at this; have := hd1 i 1; simp at this
      omega +splitDisjunctions
    }

  -- Then, each digit is nonzero, and $p_i \geq 10$.
  have p_i_ge_ten (i) : p i ≥ 10 := by
    rw [p_i_eq_add_ten_mul i]
    calc _ ≥ 10 * d i 1 := by linarith only
         _ ≥ 10 * 1 := ?_
         _ = _ := rfl
    gcongr
    rcases (hd1 i 1) with (h | h | h | h | h | h | h | h)
    any_goals simp at h
    all_goals simp [h]

  -- Primes greater than 10 are not divisible by 2 or 5, so the last digits of the primes are
  -- 1, 3, 7, or 9.
  have d_i_0_mem (i) : d i 0 ∈ ({1, 3, 7, 9} : Set ℕ) := by
    rcases (hd1 i 0) with (h | h | h | h | h | h | h | h)
    any_goals simp [h]
    any_goals suffices ¬ (p i).Prime by apply this; apply hp i

    any_goals
      apply Nat.not_prime_of_dvd_of_lt (m := 2) ?_ (by norm_num) (by linarith only [p_i_ge_ten i])
      rw [p_i_eq_add_ten_mul i, h]
      omega

    apply Nat.not_prime_of_dvd_of_lt (m := 5) ?_ (by norm_num) (by linarith only [p_i_ge_ten i])
    rw [p_i_eq_add_ten_mul i, h]
    omega

  -- Let $m_0$ be the set of last digits of the primes.
  let m0 := image (fun i ↦ d i 0) (range 4)
  -- Let $m_1$ be the set of first digits of the primes.
  let m1 := image (fun i ↦ d i 1) (range 4)

  -- As we said, $m_0 \subseteq \{1, 3, 7, 9\}$.
  have : m0 ⊆ {1, 3, 7, 9} := by
    intro
    simp [m0]
    rintro i hi rfl
    simpa using d_i_0_mem i

  -- However, as each digit is used only once, $m_0$ has 4 elements, so $m_0 = \{1, 3, 7, 9\}$.
  have m0_eq : m0 = {1, 3, 7, 9} := by
    apply (subset_iff_eq_of_card_le _).mp this
    apply le_of_eq
    symm
    convert Finset.card_image_of_injOn _ using 1
    intro i hi j hj h
    exact (hd2 i hi 0 (by simp) j hj 0 (by simp) h).1

  -- Also, as each digit is used only once, $m_0$ and $m_1$ are disjoint.
  have disjoint_m0_m1 : Disjoint m0 m1 := by
    rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_not_mem]
    intro x h
    simp [m0, m1, -mem_range] at h
    rcases h with ⟨⟨i, hi, rfl⟩, ⟨j, hj, h⟩⟩
    have := (hd2 j hj 1 (by simp) i hi 0 (by simp) h).2
    contradiction

  -- We don't use any digit other than 1, 2, 3, 4, 5, 6, 7, 9, so $m_0 \cup m_1
  -- \subseteq \{1, 2, 3, 4, 5, 6, 7, 9\}$.
  have : m0 ∪ m1 ⊆ {1, 2, 3, 4, 5, 6, 7, 9} := by
    intro
    simp [m0, m1]
    rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact hd1 i 0
    · exact hd1 i 1

  -- Again, as each digit is used only once, $m_0 \cup m_1$ has $|m_0| + |m_1$ = 4 + 4 = 8$
  -- elements, so $m_0 \cup m_1 = \{1, 2, 3, 4, 5, 6, 7, 9\}$.
  have m0_union_m1_eq : m0 ∪ m1 = {1, 2, 3, 4, 5, 6, 7, 9} := by
    apply (subset_iff_eq_of_card_le _).mp this
    apply le_of_eq
    rw [card_union_of_disjoint disjoint_m0_m1, Finset.card_image_of_injOn,
        Finset.card_image_of_injOn]; simp
    · intro i hi j hj h
      exact (hd2 i hi 1 (by simp) j hj 1 (by simp) h).1
    · intro i hi j hj h
      exact (hd2 i hi 0 (by simp) j hj 0 (by simp) h).1

  -- We showed that $m_0 = \{1, 3, 7, 9\}$, so the rest of the digits must be in $m_1$ i.e.
  -- $m_1 = \{2, 4, 5, 6\}$.
  have m1_eq : m1 = {2, 4, 5, 6} := by
    rw [disjoint_iff_ne] at disjoint_m0_m1
    ext x
    constructor
    · intro hx
      have : x ∈ ({1, 2, 3, 4, 5, 6, 7, 9} : Finset ℕ) := by
        rw [←m0_union_m1_eq]
        exact mem_union_right m0 hx
      simp at this
      rcases this with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      any_goals simp
      · apply disjoint_m0_m1 1 (by simp [m0_eq]) 1 hx rfl
      · apply disjoint_m0_m1 3 (by simp [m0_eq]) 3 hx rfl
      · apply disjoint_m0_m1 7 (by simp [m0_eq]) 7 hx rfl
      · apply disjoint_m0_m1 9 (by simp [m0_eq]) 9 hx rfl
    · simp
      rintro (hx | hx | hx | hx)
      all_goals
        have : x ∈ m0 ∪ m1 := by simp [m0_union_m1_eq, hx]
        simp at this
        rcases this with (hx' | hx')
        · simp [m0_eq, hx] at hx'
        · exact hx'

  -- Now, we can calculate the sum the primes. We have
  -- $\sum_{i=0}^3 p_i = \sum_{i=0}^3 (d_{i,0} + 10d_{i,1})
  calc ∑ i ∈ range 4, p i = ∑ i ∈ range 4, (d i 0 + 10 * d i 1) := by simp_rw [p_i_eq_add_ten_mul]
  -- $= \sum_{i=0}^3 d_{i,0} + 10 \sum_{i=0}^3 d_{i,1}$
       _ = ∑ i ∈ range 4, d i 0 + 10 * ∑ i ∈ range 4, d i 1 := by rw [sum_add_distrib, mul_sum]
  -- $= m_0.sum id + 10 m_1.sum id$
       _ = m0.sum id + 10 * ∑ i ∈ range 4, d i 1 := ?_
       _ = m0.sum id + 10 * m1.sum id := ?_
  -- $= (1 + 3 + 7 + 9) + 10 (2 + 4 + 5 + 6)$
       _ = ({1, 3, 7, 9} : Finset ℕ).sum id + 10 * ({2, 4, 5, 6} : Finset ℕ).sum id := by rw [m0_eq, m1_eq];
  -- $ = 190$
       _ = _ := by norm_num

  congr 1
  rw [sum_image]; rfl
  intro i hi j hj h
  exact (hd2 i hi 0 (by simp) j hj 0 (by simp) h).1

  congr 2
  rw [sum_image]; rfl
  intro i hi j hj h
  exact (hd2 i hi 1 (by simp) j hj 1 (by simp) h).1