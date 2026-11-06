import Mathlib

/- ## Task 4.

Let $a_{1}, a_{2}, a_{3}, \ldots$ be an infinite sequence of numbers from the set $\{1,2,3,4,5,6,7,8\}$ such that for every pair of natural numbers $(m, n)$, the conditions $a_{n} \mid n$ and $a_{m} \mid m$ are satisfied if and only if $a_{m+n}=a_{m}+a_{n}-1$.

Determine all possible values that $a_{5555}$ can take. -/
theorem number_theory_249477 (a : ℕ → ℕ) (ha : ∀ n, a n ∈ Finset.Icc 1 8)
    (h : ∀ m n, a n ∣ n ∧ a m ∣ m ↔ a (m + n) = a m + a n - 1) :
    a 5555 = 1 := by
-- we prove the sequence is constant
have my_favorite_theorem (a : ℕ → ℕ) (ha : ∀ n, a n ∈ Set.Icc 1 8)
    (h : ∀ m n, a n ∣ n ∧ a m ∣ m ↔ a (m + n) = a m + a n - 1) :
    ∀ x, a x = 1 := by
  -- base case: a 0 = 1
  have h₀ : a 0 = 1 := by
    have h₀₀ : a 0 ∣ 0 ∧ a 0 ∣ 0 ↔ a (0 + 0) = a 0 + a 0 - 1 := by
      specialize h 0 0
      simpa using h
    have h₀₁ : a 0 ∣ 0 := by
      simp [Nat.dvd_zero]
    have h₀₂ : a (0 + 0) = a 0 + a 0 - 1 := by
      simpa [h₀₁, Nat.dvd_zero, Nat.add_zero] using h₀₀
    have h₀₃ : a 0 = 1 := by
      have h₀₄ : a 0 ∈ Set.Icc 1 8 := ha 0
      have h₀₅ : 1 ≤ a 0 := h₀₄.1
      have h₀₆ : a 0 ≤ 8 := h₀₄.2
      have h₀₇ : a (0 + 0) = a 0 := by simp
      rw [h₀₇] at h₀₂
      have h₀₈ : a 0 + a 0 - 1 = a 0 := by
        omega
      have h₀₉ : a 0 = 1 := by
        omega
      exact h₀₉
    exact h₀₃
  -- base case: a 1 = 1
  have h₁ : a 1 = 1 := by
    have h₁₀ : a 1 ∣ 1 := by
      have h₁₁ : a 0 ∣ 0 ∧ a 1 ∣ 1 ↔ a (1 + 0) = a 1 + a 0 - 1 := by
        specialize h 1 0
        simpa using h
      have h₁₂ : a 0 ∣ 0 := by
        simp [Nat.dvd_zero]
      have h₁₃ : a 1 ∣ 1 := by
        by_cases h₁₄ : a 1 ∣ 1
        · exact h₁₄
        · have h₁₅ := h₁₁
          simp_all [h₀, Nat.dvd_zero, Nat.add_zero]
          <;> omega
      exact h₁₃
    have h₁₁ : a 1 = 1 := by
      have h₁₂ : a 1 ∈ Set.Icc 1 8 := ha 1
      have h₁₃ : 1 ≤ a 1 := h₁₂.1
      have h₁₄ : a 1 ≤ 8 := h₁₂.2
      have h₁₅ : a 1 ∣ 1 := h₁₀
      have h₁₆ : a 1 = 1 := by
        have h₁₇ : a 1 ∣ 1 := h₁₅
        have h₁₈ : a 1 ≤ 1 := Nat.le_of_dvd (by norm_num) h₁₇
        omega
      exact h₁₆
    exact h₁₁
  
  have h₂ : ∀ n, a n ∣ n := by
    intro n
    have h₂₁ : a n ∣ n ∧ a 0 ∣ 0 ↔ a (0 + n) = a 0 + a n - 1 := by
      specialize h 0 n
      simpa using h
    have h₂₂ : a 0 ∣ 0 := by simp [Nat.dvd_zero]
    -- from the if and only if we derive a n divides n
    have h₂₃ : a n ∣ n := by
      by_cases h₂₄ : a n ∣ n
      · exact h₂₄
      · have h₂₅ := h₂₁
        simp_all [h₀, Nat.dvd_zero, Nat.add_zero]
        <;> omega
    exact h₂₃
  -- then we prove current term equals previous term, which means the sequence is constant
  have h₃ : ∀ m, a (m + 1) = a m := by
    intro m
    have h₃₁ : a 1 ∣ 1 ∧ a m ∣ m ↔ a (m + 1) = a m + a 1 - 1 := by
      have h₃₂ := h m 1
      simpa [add_comm, add_assoc, add_left_comm] using h₃₂
    have h₃₂ : a 1 ∣ 1 := by
      simpa [h₁] using h₂ 1
    have h₃₃ : a m ∣ m := h₂ m
    have h₃₄ : a (m + 1) = a m + a 1 - 1 := by
      have h₃₅ : a 1 ∣ 1 ∧ a m ∣ m := by
        exact ⟨h₃₂, h₃₃⟩
      have h₃₆ : a (m + 1) = a m + a 1 - 1 := by
        rw [← h₃₁]
        exact h₃₅
      exact h₃₆
    have h₃₅ : a (m + 1) = a m := by
      have h₃₆ : a 1 = 1 := h₁
      rw [h₃₆] at h₃₄
      have h₃₇ : a (m + 1) = a m + 1 - 1 := by
        simpa using h₃₄
      have h₃₈ : a m + 1 - 1 = a m := by
        have h₃₉ : a m ≥ 1 := (ha m).1
        have h₄₀ : a m + 1 - 1 = a m := by
          omega
        exact h₄₀
      rw [h₃₇, h₃₈]
    exact h₃₅
  -- so we deduce it is equal to 1
  have h₄ : ∀ x, a x = 1 := by
    intro x
    have h₄₁ : ∀ n, a n = 1 := by
      intro n
      induction n with
      | zero => simp [h₀]
      | succ n ih =>
        have h₄₂ : a (n + 1) = a n := h₃ n
        have h₄₃ : a (n + 1) = 1 := by
          rw [h₄₂]
          exact ih
        exact h₄₃
    exact h₄₁ x
  
  exact h₄
-- so it can only be equal to 1
apply my_favorite_theorem <;> try assumption
simp at ha
simpa
