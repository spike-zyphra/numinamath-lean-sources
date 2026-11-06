import Mathlib

set_option maxHeartbeats 1000000

/- $2 \cdot 51$ Remove some numbers from the set $1,2,3,4, \cdots, 1982$ so that in the remaining numbers, no number is equal to the product of any two other numbers. How many numbers must be removed at a minimum to achieve this? How can this be done? -/
theorem number_theory_242020:
    IsLeast {x | ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 1982 ∧ S.card = x ∧
      ∀ n ∈ (Finset.Icc 1 1982) \ S,
      ∀ m ∈ (Finset.Icc 1 1982) \ S,
      ∀ p ∈ (Finset.Icc 1 1982) \ S,
      n ≠ m ∧ n ≠ p ∧ m ≠ p → ¬(n = m * p)} 43 := by
  rw [IsLeast.eq_1]
  constructor
  simp
  -- If the numbers 2, 3, ..., 44 are crossed out, then in the remaining numbers,
  -- no number is equal to the product of any other two numbers
  use Finset.Icc 2 44
  constructor
  decide
  -- This means that it is possible to cross out 43 numbers in such a way that the
  -- remaining numbers have the desired property
  constructor
  decide
  intro n n_lower n_upper n_removed
  intro m m_lower m_upper m_removed
  intro p p_lower p_upper p_removed
  simp at n_removed m_removed p_removed
  intro h_nm h_np h_mp
  -- Suppose that the product of two of the remaining numbers is equal to a third
  by_contra h_eq
  -- If one of the two numbers is equal to 1, then the three numbers are not distinct
  by_cases p_one: p = 1
  rw [p_one, mul_one] at h_eq
  contradiction
  have p_lower: 45 ≤ p := by omega
  by_cases m_one: m = 1
  rw [m_one, one_mul] at h_eq
  contradiction
  have m_lower: 45 ≤ m := by omega
  -- Thus the two chosen numbers are both at least 45, and so their product falls outside the initial interval
  nlinarith
  rw [lowerBounds.eq_1]
  simp
  intro a S S_sub S_card
  intro h
  -- This will be useful both to establish an upperbound for k(89 - k) in order to show
  -- that is is within the original interval, and to show that k(89 - k) is injective on [0, 44]
  have complete_square: ∀ k : ℕ, k ≤ 44 → (4 : ℤ) * k * ↑(89 - k) = 7921 - (89 - 2*k)^2 := by
    intro k k_upper
    have: ↑(89 - k) = (89 : ℤ) - ↑k := by omega
    rw [this]
    ring
  -- We consider the triplets of numbers {k, 89 - k, k(89 - k)} for k ∈ [2, 44]
  -- At least one number from each triple must be removed because otherwise
  -- k, 89 - k, and their product k(89 - k) are all among the remaining numbers
  have triplet_element: ∀ k, 2 ≤ k → k ≤ 44 → k ∈ S ∨ (89 - k) ∈ S ∨ (k * (89 - k)) ∈ S := by
    intro k k_lower k_upper
    by_contra!
    rcases this with ⟨h_k, h_89mk, h_k_89mk⟩
    have: ¬k * (89 - k) = k * (89 - k) := by
      apply h
      have: 1 ≤ 89 - k := by omega
      nlinarith
      -- We establish that k(89 - k) ≤ 1982 so that if it is not removed then it
      -- is among the remaining numbers
      zify
      have: (4 : ℤ) * k * ↑(89 - k) ≤ 7921 := by
        rw [complete_square k k_upper]
        nlinarith
      all_goals first | assumption | linarith | omega | skip
      -- If k, 89 - k, and k(89 - k) are not removed, then we only obtain a
      -- contradiction if these numbers are distinct
      by_contra h_eq
      rw [Nat.mul_eq_left] at h_eq
      omega; linarith
      by_contra h_eq
      rw [Nat.mul_eq_right] at h_eq
      linarith; omega
    contradiction
  -- Consider one of the removed elements from each triple
  let triplet_choice: ℕ → ℕ := λ k ↦
    if (k + 2) ∈ S then (k + 2) else
    if (89 - (k + 2)) ∈ S then (89 - (k + 2)) else
    if ((k + 2) * (89 - (k + 2))) ∈ S then (k + 2) * (89 - (k + 2))
    else 0
  -- The chosen element is in S, the set of removed numbers
  have triplet_in_S: ∀ k < 43, triplet_choice k ∈ S := by
    intro k k_upper
    have h_subset := triplet_element (k + 2) (by linarith) (by linarith)
    by_cases h_k: (k + 2) ∈ S
    simp [triplet_choice, h_k]
    simp [h_k] at h_subset
    by_cases h_89mk: (87 - k) ∈ S
    simp [triplet_choice, h_k, h_89mk]
    simp [h_89mk] at h_subset
    simp [triplet_choice, h_k, h_89mk, h_subset]
  have triplet_range: ∀ k < 43, triplet_choice k ∈ ({k + 2, 87 - k, (k + 2) * (87 - k)} : Set ℕ) := by
    intro k k_upper
    have h_subset := triplet_element (k + 2) (by linarith) (by linarith)
    by_cases h_k: (k + 2) ∈ S
    simp [triplet_choice, h_k]
    simp [h_k] at h_subset
    by_cases h_89mk: (87 - k) ∈ S
    simp [triplet_choice, h_k, h_89mk]
    simp [h_89mk] at h_subset
    simp [triplet_choice, h_k, h_89mk, h_subset]
  -- We show that every pair of the triples is disjoint. This then implies that
  -- the number of removed elements is at least equal to the number of triples
  have triplet_inj: ∀ i < 43, ∀ j < 43, triplet_choice i = triplet_choice j → i = j := by
    intro i i_upper j j_upper h_eq
    have: i + 2 ≥ 2 ∧ 87 - i ≥ 45 := by omega
    have: (i + 2) * (87 - i) ≥ 90 := by nlinarith
    have: j + 2 ≥ 2 ∧ 87 - j ≥ 45 := by omega
    have: (j + 2) * (87 - j) ≥ 90 := by nlinarith
    rcases triplet_range i i_upper with hi | hi | hi
    all_goals rcases triplet_range j j_upper with hj | hj | hj
    all_goals rw [hi, hj] at h_eq
    all_goals try omega
    -- k(89 - k) is too large to be equal to m or 89 - m for any m ∈ [2, 44]
    -- but we must also show that k(89 - k) ≠ m(89 - m) when k ≠ m and k, m ∈ [2, 44]
    rw [show 87 - i = 89 - (i + 2) from by omega] at h_eq
    rw [show 87 - j = 89 - (j + 2) from by omega] at h_eq
    have: (7921 : ℤ) - (89 - 2*↑(i + 2))^2 = 7921 - (89 - 2*↑(j + 2))^2 := by
      rw [← complete_square (i + 2) (by omega)]
      rw [← complete_square (j + 2) (by omega)]
      zify at h_eq
      rw [show i + (2 : ℤ) = ↑(i + 2) from rfl] at h_eq
      rw [show j + (2 : ℤ) = ↑(j + 2) from rfl] at h_eq
      rw [mul_assoc, h_eq]
      ring
    have: ((89 : ℤ) - 2 * ↑(i + 2))^2 = (89 - 2 * ↑(j + 2))^2 := by linarith
    rw [sq_eq_sq_iff_eq_or_eq_neg] at this
    rcases this with h_eq | h_neg
    omega
    omega
  rw [← S_card]
  -- We finally apply the result that the number of removed elements is at least
  -- equal to the number of triples that we were considering
  exact Finset.le_card_of_inj_on_range triplet_choice triplet_in_S triplet_inj