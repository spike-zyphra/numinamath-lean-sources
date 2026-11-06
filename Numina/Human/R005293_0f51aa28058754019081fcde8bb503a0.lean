import Mathlib

-- We will prove the following property by induction:
-- For every integer k≥3, we can find k distinct positive integers n0 < n1 < n2 < ⋯ < n(k-1) such that
-- the original condition holds and nk is even.
lemma ind (k : ℕ) (h : k ≥ 3) : ∃ n : Fin k → ℕ,
  (∀ i j, i < j → n i < n j) ∧
  (∀ i, 0 < n i) ∧
  (Even (n ⟨k - 1, by omega⟩)) ∧
  1 = ∑ i, (1 : ℚ)/(n i) := by
  revert k h
  apply Nat.le_induction
  case base =>
    -- For k=3, we indeed have 1 = 1/2 + 1/3 + 1/6 and 6 is indeed even.
    let n (i : Fin 3) : ℕ :=
      match i with
      | 0 => 2
      | 1 => 3
      | 2 => 6
    use n
    constructor
    . intro i j le
      fin_cases i <;> fin_cases j <;> simp [n] at *
    constructor
    . intro i
      fin_cases i <;> simp
    constructor
    . simp [Even]
      use 3
    . simp [Finset.sum, n]
      norm_num
  case succ =>
    -- To move from k to k+1, we will keep the numbers ni (i < k-1) unchanged
    -- and replace n(k-1) with n'(k-1) = 3n(k-1)/2 (which is an integer since n(k-1) is even)
    -- and n'k = 3n(k-1) (which is even since n(k-1) is even)
    intro k h ⟨n', ⟨h1, h2, h3, h4⟩⟩
    let last := n' ⟨k - 1, by omega⟩
    let n (i : Fin (k + 1)) : ℕ :=
      if _ : i.val = k then
        3 * last
      else if _ : i.val = k - 1 then
        3 * last / 2
      else n' ⟨i, by omega⟩
    use n
    constructor
    . -- i < j → n i < n j. We solve this goal cases by case on i and j.
      intro i j le
      have le' : i.val < j.val := by omega
      by_cases i.val = k
      . omega
      by_cases i.val = k - 1
      . have hj : ↑j = k := by omega
        simp [n]
        split <;> try omega
        specialize h2 ⟨k-1, by omega⟩
        omega
      . have hi : i.val < k - 1 := by omega
        by_cases j.val < k - 1
        . simp [n]
          repeat split <;> try omega
          specialize h1 ⟨i, by omega⟩ ⟨j, by omega⟩ (by simp; assumption)
          assumption
        . have : n i < last := by
            simp [n, last]
            split <;> try omega
            specialize h1 ⟨i, by omega⟩ ⟨k - 1, by omega⟩ (by simp; assumption)
            assumption
          suffices last ≤ n j by omega
          by_cases j.val = k - 1
          all_goals simp [n, last]; split <;> omega
    constructor
    . -- ∀ i, n i > 0. We solve this goal case by case on i.
      intro i
      by_cases i.val < k - 1
      . simp [n, last]
        repeat split <;> try omega
        specialize h2 ⟨i, by omega⟩
        assumption
      by_cases i.val = k - 1
      all_goals simp [n, last]; split <;> try specialize h2 ⟨k - 1, by omega⟩; omega
    constructor
    . -- n'k = 3n(k-1), which is even since n(k-1) is even
      simp [Even, n] at h3
      obtain ⟨r, h⟩ := h3
      use 3 * r
      simp [Even, n, last]
      omega
    . -- And the sum of the reciprocals has not changed
      -- To show this, we divide the set into two parts: {i | i < k - 1} and {i | k ≤ i + 1}
      let lower (u : ℕ) := Finset.univ.filter (fun (i : Fin u) => i < k - 1)
      let upper (u : ℕ) := Finset.univ.filter (fun (i : Fin u) => k ≤ i + 1)
      have h_union (u : ℕ) := Finset.union_compl (α := Fin u) (lower u)
      simp [lower] at h_union
      have h_disj (u : ℕ) : Disjoint (lower u) (upper u) := by
        simp [Disjoint]
        intro xs h1 h2
        apply Finset.ext
        intro x
        constructor
        . intro h
          specialize h1 h
          specialize h2 h
          simp [upper, lower] at h1 h2
          omega
        . simp
      rw [←h_union k, Finset.sum_union (h_disj k)] at h4
      rw [←h_union (k+1), Finset.sum_union (h_disj (k+1))]
      -- In the lower part, the summands are equal pointwise.
      have h_lower : ∑ i ∈ lower k, (1 : ℚ) / (n' i) = ∑ i ∈ lower (k + 1), (1 : ℚ) / (n i) := by
        apply Finset.sum_bij (fun ⟨i, _⟩ _ => ⟨i, by omega⟩)
        . intro i hi
          simp [lower]
          simp [lower] at hi
          assumption
        . intro i hi j hj
          simp
          apply Fin.eq_of_val_eq
        . intro i hi
          simp [lower] at hi
          use ⟨i, by omega⟩
          simp [lower]
          assumption
        . intro i hi
          simp [n]
          simp [lower] at hi
          repeat split <;> try omega
          rfl
      -- In the upper part, we prove the equality by calculation.
      have h_upper : ∑ i ∈ upper k, (1 : ℚ) / (n' i) = ∑ i ∈ upper (k + 1), (1 : ℚ) / (n i) := by
        have h_upper : upper k = {⟨k-1, by omega⟩} := by
          apply Finset.ext
          intro i
          constructor <;> simp [upper] <;> intro h
          . apply Fin.eq_of_val_eq
            simp
            omega
          . subst i
            norm_num
            omega
        have h_upper' : upper (k + 1) = {⟨k - 1, by omega⟩, ⟨k, by omega⟩} := by
          apply Finset.ext
          intro i
          constructor <;> simp [upper]
          . intro h
            suffices i.val = k - 1 ∨ i.val = k by
              cases this
              case' inl => left
              case' inr => right
              all_goals apply Fin.eq_of_val_eq; simp; assumption
            omega
          . rintro (h | h) <;> subst i <;> norm_num
            omega
        rw [h_upper, h_upper', Finset.sum_pair (by simp; omega)]
        simp [n, last]
        split
        . omega
        . obtain ⟨r, h3⟩ := h3
          rw [h3]
          have : 3 * (r + r) / 2 = 3 * r := by omega
          rw [this]
          field_simp
          ring
      rw [h_lower, h_upper] at h4
      assumption

/- Find 100 distinct positive integers, such that
$$
1=\frac{1}{n_{1}}+\frac{1}{n_{2}}+\cdots+\frac{1}{n_{100}}
$$ -/
theorem number_theory_607450 : ∃ n : Fin 100 → ℕ,
  (∀ i j, i ≠ j → n i ≠ n j) ∧
  (∀ i, 0 < n i) ∧
  1 = ∑ i, (1 : ℚ)/(n i) := by
  --  Now, by setting k=100, we obtain the statement
  obtain ⟨n, ⟨h1, h2, h3, h4⟩⟩ := ind 100 (by omega)
  use n
  constructor
  . intro i j h
    by_cases hord : i < j
    . specialize h1 i j hord
      omega
    . specialize h1 j i (by omega)
      omega
  . tauto
