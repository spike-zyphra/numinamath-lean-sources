import Mathlib

theorem algebra_304825 {a : ℕ → ℝ} (ha1 : a 1 = 2)
    (han : ∀ m n, m ≥ n → a (m + n) + a (m - n) - m + n = (a (2 * m) + a (2 * n)) / 2) :
    (∀ n, a (n + 2) = 2 * a (n + 1) - a n + 2) ∧
    (∑ i in Finset.Icc 1 2000, (1 / a i) < 1) := by
  -- First prove that $a_0 = 0$ using $m = n = 1$.
  have ha0 : a 0 = 0 := by 
    have h1 := han 1 1 (by norm_num) 
    norm_num at h1 
    linarith [ha1]
  -- Prove that for all $n \in \mathbf{N}$, we have $a_{n+2}=2 a_{n+1}-a_n+2$
  have h15 : ∀ (n : ℕ), a (n + 2) = 2 * a (n + 1) - a n + 2 := by
    intro n
    have eq1 := han (n + 1) 1 (by omega)
    -- Simplify arguments using specific values and known identities
    have h6 : a (2 * (n + 1 : ℕ)) = 4 * a (n + 1) - 2 * ((n + 1 : ℕ) : ℝ) := by 
      have h4 := han (n + 1) 0 (by linarith)
      simp [ha0] at h4 ⊢
      linarith 
    have eq2 : a (2 * (1 : ℕ)) = (6 : ℝ) := by 
      have h4 := han 1 0 (by linarith) 
      simp [ha0, ha1] at h4 ⊢
      linarith 
    simp [show n + 1 + 1 = n + 2 by omega, show n + 1 - 1 = n by omega, h6, eq2] at eq1
    linarith 
    all_goals linarith 
  -- Find closed form expression $a_n = n^2 + n$ using strong induction
  have h4 : ∀ (n : ℕ), a n = (n : ℝ) ^ 2 + (n : ℝ) := by
    intro n 
    induction' n using Nat.strongRecOn with n ih
    cases n with 
    | zero =>
      simp [ha0] 
      <;> norm_num 
    | succ n =>
      cases n with 
      | zero => 
        simp [ha1] 
        <;> norm_num 
      | succ n => 
        have h12 : a ((n + 1 : ℕ) + 1) = 2 * a (n + 1) - a n + 2 := by 
          apply h15 
        have h13 : a (n + 1) = ((n + 1 : ℕ) : ℝ) ^ 2 + ((n + 1 : ℕ) : ℝ) := by 
          apply ih (n + 1) 
          all_goals linarith 
        have h14 : a n = ((n : ℕ) : ℝ) ^ 2 + ((n : ℕ) : ℝ) := by 
          apply ih n 
          all_goals linarith 
        simp [h12, h13, h14] 
        <;> ring_nf 
        <;> norm_num 
        <;> ring 
  -- Prove partial sum formula using induction
  have h3 : ∀ (n : ℕ), ∑ i in Finset.Icc 1 n, (1 / a i) = 1 - 1 / ((n + 1 : ℝ)) := by
    intro n 
    induction n with 
    | zero =>
      norm_num [Finset.sum_singleton, h4]
      <;> norm_num [h4] <;> linarith 
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by norm_num)]
      rw [ih] 
      simp [h4]
      all_goals field_simp 
      <;> ring_nf 
      <;> field_simp 
      <;> ring 
  -- Prove final inequality
  have h14 : ∑ i in Finset.Icc 1 2000, (1 / a i) < 1 := by 
    rw [h3 2000] 
    norm_num 
    <;> linarith 
  constructor
  · -- Proof of first part
    intro n
    specialize h15 n 
    simpa using h15
  · -- Proof of second part
    exact h14