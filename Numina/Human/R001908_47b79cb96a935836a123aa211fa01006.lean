import Mathlib

-- The idea is, any list consists of number < 10 (actually, this premise is not necessary using method in lemma_2)
-- can be rewritten into another list with same sum and greater product.
-- But actually 1 is handled as a special case and extracted out.
lemma lemma_1 (M : List ℕ) (h1 : ∀ d ∈ M, d < 10) :
  ∃ N : List ℕ, (∀ d ∈ N, d = 2 ∨ d = 3) ∧ M.sum = N.sum + M.count 1 ∧ M.prod ≤ N.prod := by
  induction M with
  | nil => use []; simp
  | cons h t ih =>
      simp at h1
      obtain ⟨h1, h2⟩ := h1
      specialize ih h2
      obtain ⟨xs, ih, hsum, hprod⟩ := ih
      -- We do it case by case on the digit.
      interval_cases heq : h
      -- cases 2 and 3 are treated as is.
      case «2» | «3» =>
          use (h :: xs)
          rw [heq]
          simp
          constructor
          . assumption
          . omega
      -- 0 and 1 are special cases.
      case' «0» => use xs
      case' «1» => use xs
      -- for all other cases, we construct a decomposition
      case' «4» => use (2 :: 2 :: xs)
      case' «5» => use (2 :: 3 :: xs)
      case' «6» => use (3 :: 3 :: xs)
      case' «7» => use (2 :: 2 :: 3 :: xs)
      case' «8» => use (2 :: 3 :: 3 :: xs)
      case' «9» => use (3 :: 3 :: 3 :: xs)
      all_goals
      . constructor
        . try simp
          assumption
        simp
        omega

-- Then we put the extracted 1s back into the list.
lemma lemma_2 (M : List ℕ) (r : ℕ) (h1 : ∀ d ∈ M, d = 2 ∨ d = 3) (h2 : M ≠ []) :
  ∃ N : List ℕ, N ≠ [] ∧ (∀ d ∈ N, d = 2 ∨ d = 3) ∧ M.sum + r = N.sum ∧ M.prod ≤ N.prod := by
  induction r with
  | zero =>
      use M
      simp
      tauto
  | succ r ih =>
      obtain ⟨N, ⟨_, h2, h3, h4⟩⟩ := ih
      let (x :: xs) := N
      simp at *
      rcases h2 with ⟨(h1 | h1), h2⟩
      case' inl => use (3 :: xs)
      case' inr => use (2 :: 2 :: xs)
      all_goals
      . simp
        constructor
        . assumption
        subst x
        omega

-- lemma_prod_of_2_3 is about the product of a list consists of 2 and 3
lemma lemma_prod_of_2_3 (M : List ℕ) (h1 : ∀ d ∈ M, d = 2 ∨ d = 3) :
    M.prod = 3 ^ M.count 3 * 2 ^ M.count 2 := by
  induction M with
  | nil => simp
  | cons h t ih =>
      simp at h1
      rcases h1 with ⟨(h1 | h1), h2⟩
      all_goals
      . rw [h1]
        simp
        specialize ih h2
        rw [ih]
        ring_nf

-- lemma_prod_of_2_3 is about the sum of a list consists of 2 and 3
lemma lemma_sum_of_2_3 (M : List ℕ) (h1 : ∀ d ∈ M, d = 2 ∨ d = 3) :
    M.sum = 3 * M.count 3 + 2 * M.count 2 := by
  induction M with
  | nil => simp
  | cons h t ih =>
      simp at h1
      rcases h1 with ⟨(h1 | h1), h2⟩
      all_goals
      . rw [h1]
        simp
        specialize ih h2
        rw [ih]
        ring_nf

-- Any list consists of 2 and 3 with a fixed sum of 23 has a maximum product of 4374.
lemma lemma_3 (M : List ℕ)
  (h1 : ∀ d ∈ M, d = 2 ∨ d = 3) (h2 : M.sum = 23) :
  M.prod ≤ 4374 := by
  have msum := lemma_sum_of_2_3 M h1
  have : M.count 3 ≤ 7 := by
    by_contra! h
    have msum := lemma_sum_of_2_3 M h1
    omega
  -- We know the product is greater iff there are more 3 in the list.
  -- But proving the mononicity is difficuly,
  -- so we just discuss case by case on the number of 3 in the list
  interval_cases h : M.count 3
  all_goals
  . first | omega |
    have : M.count 2 = (23 - 3 * M.count 3) / 2 := by omega
    rw [lemma_prod_of_2_3 M h1, this, h]
    simp

/- Let $N$ be a positive integer whose digits add up to $23$.
  What is the greatest possible product the digits of $N$ can have? -/
theorem number_theory_44187 :
    IsGreatest {p | ∃ n, n > 0 ∧ (Nat.digits 10 n).sum = 23 ∧ (Nat.digits 10 n).prod = p} 4374 := by
  constructor
  . -- The greatest case is taken when the number consists solely of 2 and 3,
    -- and there are as many as possible 3
    use 23333333
    simp
  . simp [upperBounds]
    intros p n h hsum hp
    subst p
    have : ∀ d ∈ (Nat.digits 10 n), d < 10 := by
      intros d h
      apply Nat.digits_lt_base
      . simp
      . assumption
    -- First, we rewrite the list into some 1s and another list consists of 2 and 3.
    obtain ⟨N, hn1, hn2, hn3⟩ := lemma_1 (Nat.digits 10 n) this
    by_cases h : N = []
    . -- We handle an edge case: if there are all 1s,
      -- the product will be 1 ≤ 4374
      simp [h] at hn3
      omega
    -- Then we put 1 back into the new list
    obtain ⟨N, hn1, hn2, hn3, hn4⟩ := lemma_2 N ((Nat.digits 10 n).count 1) hn1 h
    -- And the product of the last list we obtain ≤ 4374
    have := lemma_3 N hn2
    -- And the product of each list we obtain is greater then the previous one, QED
    omega
