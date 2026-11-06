import Mathlib

/- Sot $n$ un entier strictement positif tel que $n(n+2015)$ est le carré d'un entier.
a) Prouver que $n$ n'est pas un nombre premier.
b) Donner un exemple d'un tel entier $n$. -/
/- Soit $n$ un entier strictement positif tel que $n(n+2015)$ est le carré d'un entier.
a) Prouver que $n$ n'est pas un nombre premier.
b) Donner un exemple d'un tel entier $n$. -/
theorem number_theory_604943 {n : ℕ} (hn : n > 0) (h : ∃ m, n * (n + 2015) = m ^ 2) :
    ¬ Nat.Prime n := by 
    -- Proof by contradiction: assume $n$ is prime.
  by_contra h_prime
  have h₁ : Nat.Prime n := h_prime
  -- There exists m such that $n * (n + 2015) = m^2$.
  obtain ⟨m, hm⟩ := h
  have h₂ : n * (n + 2015) = m ^ 2 := hm
  -- $n$ divides $m^2$, hence $n$ divides $m$.
  have h₃ : n ∣ m := by
    have : n ∣ m ^ 2 := by
      rw [← h₂]
      apply Nat.dvd_mul_right
    apply Nat.Prime.dvd_of_dvd_pow h₁ this
  -- Let $m = n * r$
  obtain ⟨r, hr⟩ := h₃
  have h₄ : m = n * r := hr
  -- Substitute to get $n * (n + 2015) = n^2 * r^2$.
  have h₅ : n * (n + 2015) = n ^ 2 * r ^ 2 := by
    simp [h₄, h₂]
    ring
  -- Divide both sides by $n$ (since $n > 0$).
  have h₆ : n + 2015 = n * r ^ 2 := by
    have : n * (n + 2015) = n * (n * r ^ 2) := by
      rw [h₅]
      simp [pow_two]
      ring
    exact Nat.eq_of_mul_eq_mul_left hn this
  -- Rewrite as $2015 = n * (r^2 - 1)$.
  have h₇ : 2015 = n * (r ^ 2 - 1) := by
    have : 2015 = n * r ^ 2 - n := by
      exact Nat.eq_sub_of_add_eq' h₆
    rw [this]
    simp [← Nat.mul_sub_one]
  -- $n$ divides $2015$
  have h₈ : n ∣ 2015 := by
    simp [h₇]
  -- $2015 = 5 * 13 * 31$, and $n$ is a prime dividing $2015$.
  have h₉ : 2015 = 5 * 13 * 31 := by norm_num
  -- $n$ must be one of the integers 5, 13, 31.
  have h₁₀ : n = 5 ∨ n = 13 ∨ n = 31 := by
    rw [h₉] at h₈
    have h₈₁ : n ∣ 5 * 13 * 31 := h₈
    have h₈₂ : n ∣ 5 ∨ n ∣ (13 * 31) := (Nat.Prime.dvd_mul h₁).mp h₈₁
    cases h₈₂ with
  | inl h_n5 =>
    left
    have : n ≤ 5 := Nat.le_of_dvd (by norm_num) h_n5
    have : n ≥ 2 := Nat.Prime.two_le h₁
    have : n = 5 := by
      interval_cases n <;> trivial
    exact this
  | inr h_n13_or_n31 =>
    have h₈₃ : n ∣ 13 ∨ n ∣ 31 := (Nat.Prime.dvd_mul h₁).mp h_n13_or_n31
    cases h₈₃ with
    | inl h_n13 =>
      right; left
      have : n ≤ 13 := Nat.le_of_dvd (by norm_num) h_n13
      have : n ≥ 5 := by
        have : 13 * 31 = 403 := by norm_num
        have : n ≤ 403 := Nat.le_of_dvd (by norm_num) h_n13_or_n31
        interval_cases n <;> trivial
      have : n = 13 := by interval_cases n <;> trivial
      exact this
    | inr h_n31 =>
      right; right
      have : n ≤ 31 := Nat.le_of_dvd (by norm_num) h_n31
      have : n ≥ 5 := by
        have : 13 * 31 = 403 := by norm_num
        have : n ≤ 403 := Nat.le_of_dvd (by norm_num) h_n13_or_n31
        interval_cases n <;> trivial
      have : n = 31 := by interval_cases n <;> trivial
      exact this

  -- Check the cases $n = 5, 13, 31$.
  have h₁₁ : ∀ n ∈ [5, 13, 31], ¬ ∃ r, 2015 = n * (r ^ 2 - 1) := by
    intro n hn_list
    intro h_r
    obtain ⟨r, hr⟩ := h_r
    simp [h₉] at hr
    fin_cases hn_list
    · -- $n = 5$
      have h₁₁₁ : 5 * (r ^ 2 - 1) = 5 * 13 * 31 := by simp [hr]
      have h₁₁₂ : r ^ 2 - 1 = 13 * 31 := by
        exact Nat.eq_of_mul_eq_mul_left (by norm_num) h₁₁₁
      have h₁₁₃ : r ^ 2 = 404 := by
        omega
      have h₁₁₄ : ¬ ∃ k, k ^ 2 = 404 := by
        intro h_k
        obtain ⟨k, hk⟩ := h_k
        have h₁ : 20 ^ 2 = 400 := by norm_num
        have h₂ : 21 ^ 2 = 441 := by norm_num
        have h₃ : 20 ^ 2 ≤ k ^ 2 ∧ k ^ 2 ≤ 21 ^ 2 := by
          rw [h₁, h₂, hk]
          norm_num
        have h₄ : 20 ≤ k := by
          apply (Nat.pow_le_pow_iff_left (Nat.succ_ne_zero 1)).mp
          rw [h₁]
          exact h₃.1
        have h₅ : k ≤ 21 := by
          apply (Nat.pow_le_pow_iff_left (Nat.succ_ne_zero 1)).mp
          rw [h₂]
          exact h₃.2
        interval_cases k
        · rw [h₁] at hk
          contradiction
        · rw [h₂] at hk
          contradiction
      have : ∃ k , k ^ 2 = 404 := ⟨r, h₁₁₃⟩
      contradiction
    · -- $n = 13$
      have h₁₁₅ : 13 * (r ^ 2 - 1) = 5 * 13 * 31 := by simp [hr]
      have h₁₁₆ : r ^ 2 - 1 = 5 * 31 := by
        exact Nat.eq_of_mul_eq_mul_left (by norm_num) h₁₁₅
      have h₁₁₇ : r ^ 2 = 156 := by
        omega
      have h₁₁₈ : ¬ ∃ k, k ^ 2 = 156 := by
        intro h_k
        obtain ⟨k, hk⟩ := h_k
        have h₁: 12 ^ 2 = 144 := by norm_num
        have h₂: 13 ^ 2 = 169 := by norm_num
        have h₃ : 12 ^ 2 ≤ k ^ 2 ∧ k ^ 2 ≤ 13 ^ 2 := by
          rw [h₁, h₂, hk]
          norm_num
        have h₄ : 12 ≤ k := by
          apply (Nat.pow_le_pow_iff_left (Nat.succ_ne_zero 1)).mp
          rw [h₁]
          exact h₃.1
        have h₅ : k ≤ 13 := by
          apply (Nat.pow_le_pow_iff_left (Nat.succ_ne_zero 1)).mp
          rw [h₂]
          exact h₃.2
        interval_cases k
        · rw [h₁] at hk
          contradiction
        · rw [h₂] at hk
          contradiction
      have : ∃ k , k ^ 2 = 156 := ⟨r, h₁₁₇⟩
      contradiction
    · -- $n = 31$
      have h₁₁₉ : 31 * (r ^ 2 - 1) = 5 * 13 * 31 := by simp [hr]
      have h₁₂₀ : r ^ 2 - 1 = 5 * 13 := by
        exact Nat.eq_of_mul_eq_mul_left (by norm_num) h₁₁₉
      have h₁₂₁ : r ^ 2 = 66 := by
        omega
      have h₁₂₂ : ¬ ∃ k, k ^ 2 = 66 := by
        intro h_k
        obtain ⟨k, hk⟩ := h_k
        have h₁: 8 ^ 2 = 64 := by norm_num
        have h₂: 9 ^ 2 = 81 := by norm_num
        have h₃ : 8 ^ 2 ≤ k ^ 2 ∧ k ^ 2 ≤ 9 ^ 2 := by
          rw [h₁, h₂, hk]
          norm_num
        have h₄ : 8 ≤ k := by
          apply (Nat.pow_le_pow_iff_left (Nat.succ_ne_zero 1)).mp
          rw [h₁]
          exact h₃.1
        have h₅ : k ≤ 9 := by
          apply (Nat.pow_le_pow_iff_left (Nat.succ_ne_zero 1)).mp
          rw [h₂]
          exact h₃.2
        interval_cases k
        · rw [h₁] at hk
          contradiction
        · rw [h₂] at hk
          contradiction
      have : ∃ k , k ^ 2 = 66 := ⟨r, h₁₂₁⟩
      contradiction
  -- Derive contradiction
  have h₁₂ : False := by
    cases h₁₀ with
    | inl h_n5 =>
      have : n = 5 := h_n5
      have h₁₁_n5 := h₁₁ 5 (by simp)
      apply h₁₁_n5
      -- Substitute $n$ with $5$ in $h₇$
      exact ⟨r, by simp [this] at h₇; exact h₇⟩
    | inr h_n13_or_n31 =>
      cases h_n13_or_n31 with
      | inl h_n13 =>
        have : n = 13 := h_n13
        have h₁₁_n13 := h₁₁ 13 (by simp)
        apply h₁₁_n13
        exact ⟨r, by simp [this] at h₇; exact h₇⟩
      | inr h_n31 =>
        have : n = 31 := h_n31
        have h₁₁_n31 := h₁₁ 31 (by simp)
        apply h₁₁_n31
        -- $n = 31$ in $h₇$, matching the expected type
        exact ⟨r, by simp [this] at h₇; exact h₇⟩
  contradiction

-- Part $b$,Provide an example of an integer $n$
example : ∃ n, n > 0 ∧ ∃ m, n * (n + 2015) = m ^ 2 := by
  use 1612
  constructor
  · norm_num
  · use 2418
    norm_num
