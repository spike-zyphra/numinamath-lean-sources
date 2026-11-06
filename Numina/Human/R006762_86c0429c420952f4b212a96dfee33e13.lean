import Mathlib
/- Let $N_0$ be a positive integer representing the total number of coins a person possesses. These coins are of three distinct types, with respective values of 5, 3, and 2 currency units. The total value of all coins is $V_0$ currency units. Let $x, y, z$ be the non-negative integer counts for the coins of values 5, 3, and 2 units, respectively. Thus, these quantities must satisfy the system of equations:
1. $x + y + z = N_0$
2. $5x + 3y + 2z = V_0$

Let $K = V_640875 - 2N_0$. Assume $K$ is a non-negative integer. Show that the number of distinct non-negative integer solutions $(x,y,z)$ is given by the formula:
$\max(0, \lfloor K/3 \rfloor - \max(0, \lceil (K-N_0)/2 \rceil) + 1)$. -/
theorem number_theory_640875 (n v k : ℕ) (hn : n > 0) (hv : v ≥ 2 * n) (hk : k = v - 2 * n) : {(x, y, z) : ℕ × ℕ × ℕ | x + y + z = n ∧ 5 * x + 3 * y + 2 * z = v}.ncard = k / 3 + 1 - (k + 1 - n) / 2:= by

  -- Step 1: Transform the solution set to a more manageable form
  -- Show that the original set equals a set with explicit bounds on x and explicit formulas for y, z
  have h1 : {(x, y, z) : ℕ × ℕ × ℕ | x + y + z = n ∧ 5 * x + 3 * y + 2 * z = v} = {(x, y, z) : ℕ × ℕ × ℕ | x ≥ (k + 1 - n) / 2 ∧ x ≤ k / 3 ∧ y = k - 3 * x ∧ z = n + 2 * x - k}:= by
    ext ⟨x, y, z⟩
    constructor
    .
      -- Forward direction: if (x,y,z) satisfies the original constraints, show it satisfies the new form
      intro h
      simp at h
      rcases h with ⟨h1, h2⟩
      replace hk : v = k + 2 * n:= by omega
      rw [hk] at h2
      replace h2 : 3 * x + y = k:= by linarith
      replace h1 : k + z = n + 2 * x:= by linarith
      have g1 : 2 * x ≥ k - n:= by
        suffices 2 * x + n ≥ k by omega
        linarith
      replace g1 : x ≥ (k + 1 - n) / 2:= by omega
      replace g2 : x ≤ k / 3:= by omega
      replace h1 : z = n + 2 * x - k:= by omega
      replace h2 : y = k - 3 * x:= by omega
      simp
      refine ⟨g1, g2, h2, h1⟩
    .
      -- Backward direction: if (x,y,z) satisfies the new form, show it satisfies the original constraints
      intro h
      simp at h
      rcases h with ⟨h1, h2, h3, h4⟩
      replace h1 : 2 * x ≥ k - n:= by omega
      replace h2 : 3 * x ≤ k:= by omega
      replace h3 : 3 * x + y = k:= by omega
      replace h4 : z + k = n + 2 * x:= by omega
      rw [←h3] at h4
      replace h4 : x + y + z = n:= by omega
      replace h3 : 5 * x + 3 * y + 2 * z = v:= by omega
      simp
      exact ⟨h4, h3⟩

  -- Rewrite the goal using the transformed set
  rw [h1]

  -- Define bounds for cleaner notation
  set a:= (k + 1 - n) / 2
  set b:= k / 3
  clear_value a b
  clear h1

  -- Case analysis: check if the upper bound is less than the lower bound
  by_cases hab : b < a
  .
    -- Case 1: b < a, meaning no solutions exist
    rw [show b + 1 - a = 0 by omega]
    suffices {(x, y, z) : ℕ × ℕ × ℕ | x ≥ a ∧ x ≤ b ∧ y = k - 3 * x ∧ z = n + 2 * x - k} = ∅ by rw [this] ; simp
    ext ⟨x, y, z⟩
    constructor
    .
      -- Show that any element in the set leads to a contradiction
      intro h
      simp at h
      omega
    .
      -- Empty set has no elements
      simp
  .
    -- Case 2: a ≤ b, meaning solutions exist
    simp at hab
    set c:= b - a with hc
    clear_value c
    replace hc : b = a + c:= by omega
    subst b
    clear hab
    rw [show a + c + 1 - a = c + 1 by omega]

    -- Induction on the difference c between upper and lower bounds
    induction c with
    | zero =>
      -- Base case: c = 0, meaning a = b, so there's exactly one solution
      simp
      use a, k - 3 * a, n + 2 * a - k
      ext x
      constructor
      .
        -- Show that any element in the set must be the unique solution
        intro h
        simp at h
        rw [show x = (x.1, x.2.1, x.2.2) by simp]
        rcases h with ⟨h1, h2, h3, h4⟩
        replace h1 : x.1 = a:= by omega
        rw [h3, h4, h1]
        simp
      .
        -- Show that the unique solution is in the set
        intro h
        simp at h
        subst x
        simp
    | succ c ih =>
      -- Inductive step: c > 0, meaning there are multiple solutions
      -- Show that the set can be written as the union of the previous set plus one new element
      have h1 : {(x, y, z) : ℕ × ℕ × ℕ | x ≥ a ∧ x ≤ a + (c + 1) ∧ y = k - 3 * x ∧ z = n + 2 * x - k} = insert (a + c + 1, k - 3 * (a + c + 1), n + 2 * (a + c + 1) - k) {(x, y, z) : ℕ × ℕ × ℕ | x ≥ a ∧ x ≤ a + c ∧ y = k - 3 * x ∧ z = n + 2 * x - k}:= by
        ext ⟨x, y, z⟩
        constructor
        .
          -- Forward direction: any element in the larger set is either the new element or in the smaller set
          intro h
          simp at h
          simp
          rcases h with ⟨h1, h2, h3, h4⟩
          by_cases h5 : x = a + c + 1
          .
            -- Case: x is the new element
            subst x
            left
            simp
            exact ⟨h3, h4⟩
          .
            -- Case: x is in the smaller set
            replace h2 : x ≤ a + c:= by omega
            right
            exact ⟨h1, h2, h3, h4⟩
        .
          -- Backward direction: any element in the union is in the larger set
          intro h
          simp at h
          rcases h with h | h
          .
            -- Case: the new element
            rcases h with ⟨rfl, rfl, rfl⟩
            simp
            omega
          .
            -- Case: element from the smaller set
            simp
            rcases h with ⟨h1, h2, h3, h4⟩
            refine ⟨h1, by omega, h3, h4⟩

      rw [h1]

      -- Show that the new element is not already in the smaller set
      have h2 : (a + c + 1, k - 3 * (a + c + 1), n + 2 * (a + c + 1) - k) ∉ {(x, y, z) : ℕ × ℕ × ℕ | x ≥ a ∧ x ≤ a + c ∧ y = k - 3 * x ∧ z = n + 2 * x - k}:= by
        by_contra H
        simp at H

      clear h1

      -- Define the smaller set and the new element for clarity
      set A:= {(x, y, z) : ℕ × ℕ × ℕ | x ≥ a ∧ x ≤ a + c ∧ y = k - 3 * x ∧ z = n + 2 * x - k} with hA
      set s:= (a + c + 1, k - 3 * (a + c + 1), n + 2 * (a + c + 1) - k) with hs
      clear_value A s
      clear hn hv hk

      -- Show that the smaller set is finite (needed for the cardinality calculation)
      have h3 : A.Finite:= by
        suffices A.ncard ≠ 0 by exact Set.finite_of_ncard_ne_zero this
        omega

      -- Apply the inductive hypothesis and use the cardinality formula for disjoint union
      rw [←ih]
      exact Set.ncard_insert_of_not_mem h2 h3
